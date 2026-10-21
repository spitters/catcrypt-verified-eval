/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import VerifiedEval.Fragment
public import VerifiedEval.FragmentReflect
public import VerifiedEval.FragmentFixtures
public import VerifiedEval.Arena
public import VerifiedEval.ArenaTransfer
public import VerifiedEval.FragmentCompile
public import VerifiedEval.FragmentCompileLoop
public import VerifiedEval.Block6Roundtrip
public import VerifiedEval.Block6RoundtripMem
public import VerifiedEval.FragmentCoverage
public import VerifiedEval.FragmentCoverageLoop
public import VerifiedEval.VerifiedDecide
public import VerifiedEval.VerifiedDecideHW
public import VerifiedEval.VerifiedDecideLit
public import VerifiedEval.VerifiedDecideDemo
public import VerifiedEval.VerifiedDecideHWDemo
public import VerifiedEval.VerifiedDecideLitDemo
public import VerifiedEval.Demos.VerifiedEvalDemo

/-!
# Verified native evaluation

The umbrella module of the package. A closed decidable proposition is decided by compiling
its decision procedure, written in the fragment of `VerifiedEval.Fragment`, to x86-64 bytes
with a compiler proved correct for every program of the fragment, and by one run of a fixed
x86 machine model on those bytes.

* The fragment, its reifier and fixtures: `VerifiedEval.Fragment`,
  `VerifiedEval.FragmentReflect`, `VerifiedEval.FragmentFixtures`.
* The transfer front from spec types to a byte arena: `VerifiedEval.Arena`,
  `VerifiedEval.ArenaTransfer`.
* The compilers and their correctness theorems: `VerifiedEval.FragmentCompile`,
  `VerifiedEval.FragmentCompileLoop`.
* Coverage and byte round trip of the compiler output: `VerifiedEval.Block6Roundtrip`,
  `VerifiedEval.Block6RoundtripMem`, `VerifiedEval.FragmentCoverage`,
  `VerifiedEval.FragmentCoverageLoop`.
* The tactics `verified_decide`, `verified_decide_hw`, `verified_decide_lit` and their
  soundness theorems: `VerifiedEval.VerifiedDecide`, `VerifiedEval.VerifiedDecideHW`,
  `VerifiedEval.VerifiedDecideLit`.
* One demo per tactic and a worked example: `VerifiedEval.VerifiedDecideDemo`,
  `VerifiedEval.VerifiedDecideHWDemo`, `VerifiedEval.VerifiedDecideLitDemo`,
  `VerifiedEval.Demos.VerifiedEvalDemo`.

The hardware and literal demos run the runner `VerifiedEval/runner/vrun` when they are
elaborated; it is built from `VerifiedEval/runner/vrun.c` beforehand, or named by the
environment variable `CATCRYPT_VRUN`.
-/
