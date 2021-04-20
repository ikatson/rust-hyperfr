// DS field should be equal to 0 for simplicity as we seem to have only 36 bits of address anyway.
// DS field is used when larger addresses.

// We also can have only 1 translation table

/*
A System register bit enables the stage of address translation, SCTLR_ELx.M or HCR_EL2.VM.
SCTLR_ELx.M:
0 - EL1&0 stage 1 address translation disabled
1 - EL1&0 stage 1 address translation enabled.
- Also need to consider bit I:
  -

A System register bit determines the endianness of the translation table lookups, SCTLR_ELx.EE.
A Translation Control Register (TCR_ELx) controls the stage of address translation.
*/
