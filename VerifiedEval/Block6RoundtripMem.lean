/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.EncodeJBlock6Roundtrip

/-!
# Byte-stream round trip for the indexed memory moves and `CMP`

The indexed memory moves are inverted by `SailX86Decoder.decodeJ1` itself
(`roundtrip_loadMemIdx`, `roundtrip_storeMemIdx`), and the compares by the
`decodeCmp` arm of `decodeJ1_6`; the covered set `blockCovered6` and the block
round trip `roundtrip_block6` are
`CatCrypt.Crypto.SecureCompilation.X86Backend.EncodeJBlock6Roundtrip` in the
compiler package; this module re-exports it.
-/
