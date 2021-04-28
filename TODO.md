Translation refactor todo:
- [ ] Remove hard-coded txsz etc
- [ ] Ensure translation tables are not overlapping with DRAM once DRAM is initialized.
   They proably alias now and it might cause really bad bugs.
   Actually, they don't, but as they are mapped earlier than translation tables are filled,
   they are writeable by the "armos" kernel, which is a smell.

- [ ] 2048 - it's hardcoded, but shouldn't be.
  For example, top level supports only a couple entries.
  For 4kb, only 512 entry tables might exist.
  But for 64kb, 8192 entry tables might exist.
- [ ] Test with 4kb