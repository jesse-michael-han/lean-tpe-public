"""
  Wrapper script for running the evaluation script in parallel on the declarations in a .names file
"""
import pickle as pkl
import os
import itertools
import numpy as np
import subprocess
from tqdm import tqdm
from multiprocessing.pool import ThreadPool
import re
from pathlib import Path
import datetime

def files_with_extension(dir_path, ext=None):
    if ext is None:
        dataset_files = [os.path.join(dir_path, x) for x in os.listdir(dir_path)]
    else:
        dataset_files = [os.path.join(dir_path, x) for x in os.listdir(dir_path) if re.search(r"." + ext, x)] # TODO(jesse): test
    return dataset_files

def _parse_main():
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("n_workers", type=int)
    parser.add_argument("decls_per_shard", type=int)
    parser.add_argument("decls_file")
    parser.add_argument("dest_dir")
    parser.add_argument("--max_tokens", type=int)
    parser.add_argument("--temperature", type=float)
    parser.add_argument("--top_p", type=float)
    parser.add_argument("--n", type=int)
    parser.add_argument("--best_of", type=int)
    parser.add_argument("--fuel", type=int)
    parser.add_argument("--engine_id")
    parser.add_argument("--api_key")
    parser.add_argument("--nbest", type=int)
    parser.add_argument("--beam", type=int)
    parser.add_argument("--model_path")
    parser.add_argument("--data_path")
    parser.add_argument("--entry_pt")
    parser.add_argument("--max_width", help="maximum size of search queue for BFS")
    parser.add_argument("--max_depth", help="maximum distance of search node from root before the search queue rejects it")

    parser.add_argument("--lean_threads", help="number of threads per Lean process", default=None)
    parser.add_argument("--lean_timeout", help="deterministic timeout for Lean process in millions of allocations. Interactive default is one. Default is unbounded (none).", default=None)

    parser.add_argument("--api", default="gptf", 
        help="gptf|baseline|fairseq")
    parser.add_argument("--search_strategy", default="greedy", help="greedy|bfs")
    parser.add_argument("--tac_timeout", default=5, help="tactic execution timeout (s)", type=int)
    parser.add_argument("--global_timeout", default=300, help="proof search timeout (s)", type=int)
    return parser.parse_args()

def eval_decls_step(decl_file: str, dest: str, opts):
    strat = opts.search_strategy
    try:
        assert strat in ["bfs", "greedy"]
    except AssertionError:
        raise Exception("[parallel_eval] ERROR: must specify `search_strategy` = `bfs` or `greedy`")

    if not opts.api == "baseline":
        try:
            assert opts.n <= opts.best_of
        except AssertionError:
            raise Exception(f"[parallel_eval] ERROR: opts.n ({opts.n}) must be less than or equal to opts.best_of ({opts.best_of})")
    if strat == "bfs" and (opts.max_width is None or opts.max_depth is None):
        raise Exception("[parallel_eval] ERROR: max_width and max_depth must be set for BFS")
    if opts.api == "baseline":
        lean_script = f"./src/evaluation/{strat}/baseline.lean" 
    elif opts.api == "gptf": 
        lean_script = f"./src/evaluation/{strat}/gptf.lean" 
    elif opts.api =="fairseq": 
        lean_script = f"./src/evaluation/{strat}/fairseq.lean"
    lean_cmd = ["lean"]
    lean_cmd += [f"--threads={opts.lean_threads}"] if opts.lean_threads is not None else []
    lean_cmd += [f"--timeout={opts.lean_timeout}000000"] if opts.lean_timeout is not None else []
    lean_cmd += ["--run"]
    lean_cmd += [lean_script] # TODO(jesse): don't use relative path
    lean_cmd += [decl_file]
    lean_cmd += [dest]
    if opts.api == "baseline":
        lean_cmd += list(map(str, [opts.fuel, opts.tac_timeout, opts.global_timeout])) if strat == "greedy" else list(map(str, [opts.fuel, opts.max_width, opts.max_depth, opts.tac_timeout, opts.global_timeout]))
    elif opts.api == "gptf":
        if strat == "greedy":
          extra_args = [opts.max_tokens, opts.temperature, opts.top_p, opts.n, opts.best_of, opts.fuel, opts.engine_id, opts.api_key, opts.tac_timeout, opts.global_timeout]
        else: # bfs
          extra_args = [opts.max_tokens, opts.temperature, opts.top_p, opts.n, opts.best_of, opts.fuel, opts.max_width, opts.max_depth, opts.engine_id, opts.api_key, opts.tac_timeout, opts.global_timeout]
        assert not any(x is None for x in extra_args)
        lean_cmd += list(map(str, extra_args))
    elif opts.api == "fairseq":
        # TODO(yuhuai)
        extra_args = [opts.max_tokens, opts.temperature, opts.nbest, opts.beam, opts.fuel, opts.entry_pt, opts.model_path, opts.data_path, opts.tac_timeout, opts.global_timeout]
        assert not any(x is None for x in extra_args)
        lean_cmd += list(map(str, extra_args))

    path = Path(dest)
    stdout_dest = os.path.join(str(path.parent), str(path.stem) + ".out")
    with open(stdout_dest, "w") as f:
      subprocess.run(lean_cmd, stdout=f, stderr=f)
    return (decl_file, lean_cmd)

# tracks the set of completed tasks
class EvaluationState:
    def __init__(self, decl_files):
        self.done_dict = {decl_file:False for decl_file in decl_files}

    def retrieve_tasks(self):
        return [k for k,v in self.done_dict.items() if not v]

    def register_finished(self, task):
        self.done_dict[task] = True

def _main(opts):
    decls_file = opts.decls_file
    dest_dir = opts.dest_dir
    n_workers = opts.n_workers
    decls_per_shard = opts.decls_per_shard
    with open(decls_file, "r") as f:
        decls = f.readlines()

    num_shards = len(decls)//decls_per_shard

    batch_size = decls_per_shard

    batches = [decls[i*batch_size:(i+1)*batch_size] for i in range(num_shards-1)] + [decls[batch_size*(num_shards-1):]]

    split_decls_dir = os.path.join(dest_dir, "split_decls/")
    if not os.path.exists(split_decls_dir):
        os.makedirs(split_decls_dir)

    decl_files = []
    for i, batch in enumerate(batches):
        decl_file = os.path.join(split_decls_dir, f"shard_{i}.names")
        with open(decl_file, "w") as f:
            for decl in batch:
                f.write(decl)
        decl_files.append(decl_file)

    eval_decls_state_path = os.path.join(dest_dir, "eval_decls_state.pkl")

    parallel_eval_log_path = os.path.join(dest_dir, "parallel_eval.log")

    if os.path.exists(eval_decls_state_path):
        with open(eval_decls_state_path, "rb") as f:
            eval_decls_state = pkl.load(f)
    else:
        eval_decls_state = EvaluationState(decl_files)

    dests = [os.path.join(dest_dir, f"shard_{i}.json") for i in range(len(batches))]

    pool_args = [(decl_file, dest, opts) for decl_file, dest in zip(eval_decls_state.retrieve_tasks(), dests)]
    with ThreadPool(n_workers) as pool:
        finished_count = 0
        for (decl_file, lean_cmd) in tqdm(pool.imap_unordered((lambda x: eval_decls_step(*x)), pool_args), total=len(decl_files)):
            finished_count += 1
            print(f"{finished_count} JOBS FINISHED")
            eval_decls_state.register_finished(decl_file)
            with open(parallel_eval_log_path, "a") as f:
                lean_cmd = " ".join(lean_cmd)
                f.write(f"[parallel_eval] {datetime.datetime.now()} FINISHED JOB: {decl_file}\n")
                f.write(f"[parallel_eval] {datetime.datetime.now()} LEAN COMMAND: {lean_cmd}\n")
            with open(eval_decls_state_path, "wb") as f:
                pkl.dump(eval_decls_state, f)

if __name__ == "__main__":
    opts = _parse_main()
    _main(opts)
