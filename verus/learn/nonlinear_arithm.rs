use vstd::prelude::*;

verus! {
    fn main() {}

    proof fn bound_check(x: u32, y: u32, z: u32)
    requires
        x <= 8,
        y <= 8,
    {
        assert(x * y <= 100) by (nonlinear_arith)
            requires
                x <= 10,
                y <= 10;

        assert(x * y <= 1000);
    }

    proof fn bound_check2(x: u32, y: u32, z: u32) by (nonlinear_arith)
    requires
        x <= 8,
        y <= 8,
    ensures
        x * y <= 64
    { }

    pub proof fn lemma_mod_difference_equal_helper(x: int, y:int, d:int, small_x:int, small_y:int, tmp1:int, tmp2:int)// by(integer_ring)
    by (nonlinear_arith)
    requires
        small_x == x % d,
        small_y == y % d,
        tmp1 == (small_y - small_x) % d,
        tmp2 == (y - x) % d,
    ensures
        (tmp1 - tmp2) % d == 0
    {
        assume(false);

    }
    pub proof fn lemma_mod_difference_equal(x: int, y: int, d: int) by(nonlinear_arith)
    requires
        d > 0,
        x <= y,
        x % d <= y % d,
        y - x < d
    ensures
        y % d - x % d == y - x
    {
        let small_x = x % d;
        let small_y = y % d;
        let tmp1 = (small_y - small_x) % d;
        let tmp2 = (y - x) % d;
        lemma_mod_difference_equal_helper(x,y,d, small_x, small_y, tmp1, tmp2);
    }

    pub proof fn lemma_mod_between_helper(x: int, y: int, d: int, small_x:int, small_y:int, tmp1:int) 
    //by(integer_ring)
    requires
        small_x == x % d,
        small_y == y % d,
        tmp1 == (small_x - small_y) % d,
    ensures
        (tmp1 - (x-y)) % d == 0
    {
        assume(false);
    }

    // note that below two facts are from the helper function, and the rest are done by `by(nonlinear_arith)`.
    // x % d - y % d == x - y  (mod d)
    // y % d - z % d == y - z  (mod d)
    pub proof fn lemma_mod_between(d: int, x: int, y: int, z: int) by(nonlinear_arith)
    requires
        d > 0,
        x % d < y % d,
        y - x <= d,
        x <= z < y
    ensures
        x % d <= z % d < y % d
    {
        let small_x = x % d;
        let small_y = y % d;
        let small_z = z % d;
        let tmp1 = (small_x - small_z) % d;
        lemma_mod_between_helper(x,z,d, small_x, small_z, tmp1);

        let tmp2 = (small_z - small_y) % d;
        lemma_mod_between_helper(z,y,d, small_z, small_y, tmp2);    
    }

    pub proof fn multiple_offsed_mod_gt_0_helper(a: int, b: int, c: int, ac: int, bc: int, abc: int) 
    //by (integer_ring)
    requires
        ac == a % c,
        bc == b % c,
        abc == (a - b) % c,
    ensures (ac - bc - abc) % c == 0
    {
        assume(false);
    }

    pub proof fn multiple_offsed_mod_gt_0(a: nat, b: nat, c: nat) by (nonlinear_arith) 
    requires
        a > b,
        c > 0,
        b % c == 0,
        a % c > 0,
    ensures (a - b) % (c as int) > 0
    {
        multiple_offsed_mod_gt_0_helper(
            a as int, 
            b as int, 
            c as int, 
            (a % c) as int, 
            (b % c) as int, 
            ((a - b) % (c as int)) as int
        );
    }

    pub proof fn multiple_offsed_mod_gt_0_2(a: nat, b: nat, c: nat) by (nonlinear_arith)
    requires
        a > b,
        c > 0,
        b % c == 0,
        a % c > 0,
    ensures (a - b) % (c as int) > 0
    { 
        assume(false);
    }
    
}

