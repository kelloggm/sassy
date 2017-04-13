Require ImpInterp.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatBigInt.
Require Import ExtrOcamlZBigInt.
Require Import ExtrOcamlString.

Extraction Blacklist Nat.
Extraction Blacklist List.
Extraction Blacklist String.

Extract Constant ImpCommon.extcall =>
  "ImpLib.extcall".

Cd "Imp/extract".
Separate Extraction
  ImpInterp.interp_p.
Cd "../..".