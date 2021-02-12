import system.io
import tactic

meta def main : tactic unit := do {
  tactic.try_for_time 5000 $ do {
    ([1,2,3,4,5,6,7,8,9,10] : list ℕ).mmap' (λ k, tactic.try_for_time 1000 $ do {
      tactic.sleep (250 * k),
      tactic.trace format!"NUM: {k}"
    })
  }
}

-- #eval main
