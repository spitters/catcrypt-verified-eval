import Lake
open Lake DSL

-- Verified native evaluation: a decision procedure written in a fragment of Lean is
-- compiled to x86-64 bytes by a compiler proved correct for every program of the
-- fragment, and a closed decidable proposition follows from one run of a fixed x86
-- machine model on those bytes. The compiler's target semantics, the byte encoder and
-- the decoder with its round trip come from `catcryptCompiler`; the transfer front uses
-- `paramTransfer`.

package catcryptVerifiedEval where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]
  -- `-E <kind>` reports Lean messages of that kind as errors. `hasSorry` is the
  -- kind Lean attaches to a declaration whose proof term reaches `sorryAx`, so
  -- building this package refuses such a declaration and no separate step has to
  -- read the build's output. The word in a comment, a docstring or a string
  -- literal carries no such message; a declaration reaching `sorryAx` through a
  -- tactic carries one even though the word appears nowhere in its source.
  moreLeanArgs := #["-E", "hasSorry"]
  -- A memory limit turns a build that would be OOM-killed into a `(kernel) excessive
  -- memory consumption` error at a file and line. It is a weak argument so that it
  -- does not enter the build trace: raising or lowering it rebuilds nothing.
  weakLeanArgs := #["-M", "8000"]

-- The umbrella `VerifiedEval` and every module under `VerifiedEval/`. The demos
-- `VerifiedDecideHWDemo` and `VerifiedDecideLitDemo` run the runner
-- `VerifiedEval/runner/vrun` when they are elaborated: build it first with
-- `cc -O2 -o VerifiedEval/runner/vrun VerifiedEval/runner/vrun.c`, or name a runner
-- by the environment variable `CATCRYPT_VRUN`.
@[default_target]
lean_lib VerifiedEval where
  globs := #[.andSubmodules `VerifiedEval]

-- The sibling packages of the CatCrypt workspace, as local path dependencies. Their
-- own requirements (CompPoly, VeIR and the others of `catcryptCompiler`) are resolved
-- transitively; a requirement stated here takes precedence over a dependency's
-- requirement of the same package.
require catcryptCompiler from "../catcrypt-compiler"
require paramTransfer from "../ParamTransfer"
require catcryptCore from "../CatCrypt-core"
require «hax-lean» from "../hax-lean"

-- Mathlib last, so that its versions of the shared dependencies (Batteries, Aesop,
-- ProofWidgets) win on conflicts. The tag is the one every package of the workspace
-- pins (commit 0df444a360eaa60ab8c11dca51a86af692955474).
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.35.0"
