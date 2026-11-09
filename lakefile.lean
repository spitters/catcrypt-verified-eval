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

-- The CatCrypt packages at the revisions the compiler pins. Their own requirements
-- (CompPoly, VeIR and the others of `catcryptCompiler`) are resolved transitively; a
-- requirement stated here takes precedence over a dependency's requirement of the same
-- package. Inside the CatCrypt workspace the top-level package requires all four as
-- local paths, and its requirements take precedence over these.
require catcryptCompiler from git
  "https://github.com/spitters/catcrypt-compiler.git" @ "44123ebe51a07786db8901f29018937c84630f26"
require paramTransfer from git
  "https://github.com/spitters/ParamTransfer.git" @ "40916765d6df5954da9105db764858233cdada86"
require catcryptCore from git
  "https://github.com/spitters/CatCrypt-core.git" @ "130e2e7848757df39f0021d57f183b66062ba1ef"
require «hax-lean» from git
  "https://github.com/spitters/hax-lean.git" @ "918bdd1985c7669dce192e01521a445752994971"

-- Mathlib last, so that its versions of the shared dependencies (Batteries, Aesop,
-- ProofWidgets) win on conflicts. The tag is the one every package of the workspace
-- pins (commit 0df444a360eaa60ab8c11dca51a86af692955474).
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.35.0"
