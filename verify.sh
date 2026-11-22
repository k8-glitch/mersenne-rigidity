#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "$0")" && pwd)"
repo="$root/mathlib4"
commit=c98ae54af00eaefe79c51b2b278361ca94e59bfb
if [[ ! -d "$repo" ]]; then
  git clone --depth 1 --branch v4.25.2 https://github.com/leanprover-community/mathlib4.git "$repo"
fi
cd "$repo"
[[ "$(git rev-parse HEAD)" == "$commit" ]] || { echo "Unexpected mathlib revision" >&2; exit 1; }
lake exe cache get Mathlib/RingTheory/Coprime/Lemmas.lean Mathlib/Data/Nat/Factorization/Basic.lean Mathlib/Algebra/Ring/Int/Parity.lean Mathlib/Tactic/LinearCombination.lean Mathlib/Tactic/Linarith.lean Mathlib/Tactic/IntervalCases.lean Mathlib/Tactic/Positivity.lean
lake env lean "$root/MersenneRigidity.lean"
