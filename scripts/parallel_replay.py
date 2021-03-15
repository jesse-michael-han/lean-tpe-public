import glob
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
import jsonlines

def files_with_extension(dir_path, ext=None):
    if ext is None:
        dataset_files = [os.path.join(dir_path, x) for x in os.listdir(dir_path)]
    else:
        dataset_files = [os.path.join(dir_path, x) for x in os.listdir(dir_path) if re.search(r"." + ext, x)]
    return dataset_files

def _parse_main():
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("n_workers", type=int)
    parser.add_argument("result_dir", type=str)
    parser.add_argument("dest_dir", type=str)    
    parser.add_argument("names_file", type=str)
    return parser.parse_args()

def replay_proofs_step(
        shard: str,
        dest: str,
        names_file: str
):
    lean_cmd = ["lean"]
    lean_cmd += ["--run"]
    lean_cmd += ["./src/tools/proof_replay.lean"]
    lean_cmd += [shard, dest, names_file]
    path = Path(dest)
    stdout_dest = os.path.join(str(path.parent), str(path.stem) + ".out")
    with open(stdout_dest, "w") as f:
        subprocess.run(lean_cmd, stdout=f, stderr=f)
    return (shard, lean_cmd)

def _main(opts):
    names_file = opts.names_file
    result_dir = opts.result_dir
    n_workers = opts.n_workers
    dest_dir = opts.dest_dir

    if not os.path.exists(dest_dir):
        os.makedirs(dest_dir)

    parallel_eval_log_path = os.path.join(dest_dir, "parallel_replay.log")

    shards = glob.glob(os.path.join(result_dir, "*.json"))
    print(f"GOT {len(shards)} SHARDS")
    def get_dest(shard):
        path = Path(shard)
        return os.path.join(dest_dir, path.stem + "_shorter_proof.json")
    
    pool_args = [(shard, get_dest(shard), names_file) for shard in shards]
    with ThreadPool(n_workers) as pool:
        finished_count = 0
        for (shard, lean_cmd) in tqdm(pool.imap_unordered((lambda x: replay_proofs_step(*x)), pool_args), total=len(shards)):
            finished_count += 1
            print(f"{finished_count} JOBS FINISHED")
            with open(parallel_eval_log_path, "a") as f:
                lean_cmd = " ".join(lean_cmd)
                f.write(f"[parallel_eval] {datetime.datetime.now()} FINISHED JOB: {shard}\n")
                f.write(f"[parallel_eval] {datetime.datetime.now()} LEAN COMMAND: {lean_cmd}\n")

    shorter_proofs = []
    shorter_proof_shards = glob.glob(os.path.join(dest_dir, "*_shorter_proof.json"))
    for shorter_proof_shard in shorter_proof_shards:
        with jsonlines.open(shorter_proof_shard, "r") as f:
            for jsonline in f:
                shorter_proofs.append(jsonline)

    key = (lambda x: float(x[1])/x[0])

    shorter_proofs = sorted(shorter_proofs, key=key)
                
    with jsonlines.open(os.path.join(dest_dir, "summary.json"), "w") as f:
        for l in shorter_proofs:
            f.write(l)
    print(f"FOUND {len(shorter_proofs)} SHORTER PROOFS")

if __name__ == "__main__":
    opts = _parse_main()
    _main(opts)
