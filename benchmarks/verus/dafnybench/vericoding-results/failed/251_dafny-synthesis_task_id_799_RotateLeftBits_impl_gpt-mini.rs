use vstd::prelude::*;

verus! {

// <vc-helpers>
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
fn rotate_left_bits(n: u32, d: int) -> (result: u32)
    requires 0 <= d < 32
    ensures result == ((n << d) | (n >> (32 - d)))
// </vc-spec>
// <vc-code>
{
    proof {
        assert(0 <= d);
        assert(d < 32);
    }

    if d == 0 {
        let res: u32 = (n << 0usize) | (n >> 32usize);
        proof {
            assert(res == ((n << 0) | (n >> (32 - 0))));
        }
        res
    } else if d == 1 {
        let res: u32 = (n << 1usize) | (n >> 31usize);
        proof {
            assert(res == ((n << 1) | (n >> (32 - 1))));
        }
        res
    } else if d == 2 {
        let res: u32 = (n << 2usize) | (n >> 30usize);
        proof {
            assert(res == ((n << 2) | (n >> (32 - 2))));
        }
        res
    } else if d == 3 {
        let res: u32 = (n << 3usize) | (n >> 29usize);
        proof {
            assert(res == ((n << 3) | (n >> (32 - 3))));
        }
        res
    } else if d == 4 {
        let res: u32 = (n << 4usize) | (n >> 28usize);
        proof {
            assert(res == ((n << 4) | (n >> (32 - 4))));
        }
        res
    } else if d == 5 {
        let res: u32 = (n << 5usize) | (n >> 27usize);
        proof {
            assert(res == ((n << 5) | (n >> (32 - 5))));
        }
        res
    } else if d == 6 {
        let res: u32 = (n << 6usize) | (n >> 26usize);
        proof {
            assert(res == ((n << 6) | (n >> (32 - 6))));
        }
        res
    } else if d == 7 {
        let res: u32 = (n << 7usize) | (n >> 25usize);
        proof {
            assert(res == ((n << 7) | (n >> (32 - 7))));
        }
        res
    } else if d == 8 {
        let res: u32 = (n << 8usize) | (n >> 24usize);
        proof {
            assert(res == ((n << 8) | (n >> (32 - 8))));
        }
        res
    } else if d == 9 {
        let res: u32 = (n << 9usize) | (n >> 23usize);
        proof {
            assert(res == ((n << 9) | (n >> (32 - 9))));
        }
        res
    } else if d == 10 {
        let res: u32 = (n << 10usize) | (n >> 22usize);
        proof {
            assert(res == ((n << 10) | (n >> (32 - 10))));
        }
        res
    } else if d == 11 {
        let res: u32 = (n << 11usize) | (n >> 21usize);
        proof {
            assert(res == ((n << 11) | (n >> (32 - 11))));
        }
        res
    } else if d == 12 {
        let res: u32 = (n << 12usize) | (n >> 20usize);
        proof {
            assert(res == ((n << 12) | (n >> (32 - 12))));
        }
        res
    } else if d == 13 {
        let res: u32 = (n << 13usize) | (n >> 19usize);
        proof {
            assert(res == ((n << 13) | (n >> (32 - 13))));
        }
        res
    } else if d == 14 {
        let res: u32 = (n << 14usize) | (n >> 18usize);
        proof {
            assert(res == ((n << 14) | (n >> (32 - 14))));
        }
        res
    } else if d == 15 {
        let res: u32 = (n << 15usize) | (n >> 17usize);
        proof {
            assert(res == ((n << 15) | (n >> (32 - 15))));
        }
        res
    } else if d == 16 {
        let res: u32 = (n << 16usize) | (n >> 16usize);
        proof {
            assert(res == ((n << 16) | (n >> (32 - 16))));
        }
        res
    } else if d == 17 {
        let res: u32 = (n << 17usize) | (n >> 15usize);
        proof {
            assert(res == ((n << 17) | (n >> (32 - 17))));
        }
        res
    } else if d == 18 {
        let res: u32 = (n << 18usize) | (n >> 14usize);
        proof {
            assert(res == ((n << 18) | (n >> (32 - 18))));
        }
        res
    } else if d == 19 {
        let res: u32 = (n << 19usize) | (n >> 13usize);
        proof {
            assert(res == ((n << 19) | (n >> (32 - 19))));
        }
        res
    } else if d == 20 {
        let res: u32 = (n << 20usize) | (n >> 12usize);
        proof {
            assert(res == ((n << 20) | (n >> (32 - 20))));
        }
        res
    } else if d == 21 {
        let res: u32 = (n << 21usize) | (n >> 11usize);
        proof {
            assert(res == ((n << 21) | (n >> (32 - 21))));
        }
        res
    } else if d == 22 {
        let res: u32 = (n << 22usize) | (n >> 10usize);
        proof {
            assert(res == ((n << 22) | (n >> (32 - 22))));
        }
        res
    } else if d == 23 {
        let res: u32 = (n << 23usize) | (n >> 9usize);
        proof {
            assert(res == ((n << 23) | (n >> (32 - 23))));
        }
        res
    } else if d == 24 {
        let res: u32 = (n << 24usize) | (n >> 8usize);
        proof {
            assert(res == ((n << 24) | (n >> (32 - 24))));
        }
        res
    } else if d == 25 {
        let res: u32 = (n << 25usize) | (n >> 7usize);
        proof {
            assert(res == ((n << 25) | (n >> (32 - 25))));
        }
        res
    } else if d == 26 {
        let res: u32 = (n << 26usize) | (n >> 6usize);
        proof {
            assert(res == ((n << 26) | (n >> (32 - 26))));
        }
        res
    } else if d == 27 {
        let res: u32 = (n << 27usize) | (n >> 5usize);
        proof {
            assert(res == ((n << 27) | (n >> (32 - 27))));
        }
        res
    } else if d == 28 {
        let res: u32 = (n << 28usize) | (n >> 4usize);
        proof {
            assert(res == ((n << 28) | (n >> (32 - 28))));
        }
        res
    } else if d == 29 {
        let res: u32 = (n << 29usize) | (n >> 3usize);
        proof {
            assert(res == ((n << 29) | (n >> (32 - 29))));
        }
        res
    } else if d == 30 {
        let res: u32 = (n << 30usize) | (n >> 2usize);
        proof {
            assert(res == ((n << 30) | (n >> (32 - 30))));
        }
        res
    } else {
        // d == 31
        let res: u32 = (n << 31usize) | (n >> 1usize);
        proof {
            assert(res == ((n << 31) | (n >> (32 - 31))));
        }
        res
    }
}
// </vc-code>

fn main() {
}

}