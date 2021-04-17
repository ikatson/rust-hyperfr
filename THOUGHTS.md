So say an address is 48 bits.

0xffff_ffff_ffff

If the granule is e.g. 16kb, it means actual physical pages are 16kb.
16kb = 0x3fff, which is 14 bits.

So bottom 34 bits are not usable for translation - they indicate the actuall address in the last level granule.
More than that,

It means only upper 24 bits are available.
If split evenly for a 2-stage table, it would allow for 12 bits level 1, 12 bits level 2.

12 bits is 4096 entries at most.

If an entry is e.g.

struct {
    next + flags: u64,
}

then the first level would take 32kb only, however level 2 at most would take 134mb, which is pretty insane