/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.EncodeJBlock6Roundtrip

/-!
# Byte-stream round trip for the shipped encoder `encodeJBlock6`

The decoder `decodeJ1_6`/`decodeJStream6` for the shipped encoder and the round
trip `roundtrip_block6` are `CatCrypt.Crypto.SecureCompilation.X86Backend.EncodeJBlock6Roundtrip`
in the compiler package; this module re-exports it.
-/
