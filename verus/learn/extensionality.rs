
use vstd::prelude::*;

verus! {
    fn main() {
    }
    
    proof fn check_eq(x: Seq<int>, y: Seq<int>)
    requires
        x == y,
    {
    }

    proof fn test_eq2() {
        let s1: Seq<int> = seq![0, 10, 20, 30, 40];
        let s2: Seq<int> = seq![0, 10] + seq![20] + seq![30, 40];
        let s3: Seq<int> = Seq::new(5, |i: int| 10 * i);
        assert(s1 =~= s2);
        assert(s1 =~= s3);
        check_eq(s1, s2); // succeeds
        check_eq(s1, s3); // succeeds
    }

    #[verifier::ext_equal]
    struct Foo {
        a: Seq<int>,
        b: Set<int>,
    }

    proof fn ext_equal_struct() {
        let f1 = Foo { a: seq![1, 2, 3], b: set!{4, 5, 6} };
        let f2 = Foo { a: seq![1, 2].push(3), b: set!{5, 6}.insert(4) };
        assert(f1 == f2);    // FAILS -- need to use =~= first
        assert(f1.a =~= f2.a);  // succeeds
        assert(f1.b =~= f2.b);  // succeeds
        assert(f1 == f2);  // succeeds, now that we've used =~= on .a and .b
    }

    proof fn ext_equal_nested() {
        let inner: Set<int> = set!{1, 2, 3};
        let s1: Seq<Set<int>> = seq![inner];
        let s2 = s1.update(0, s1[0].insert(1));
        let s3 = s1.update(0, s1[0].insert(2).insert(3));
        // assert(s2 =~= s3); // FAILS
        assert(s2 =~~= s3);  // succeeds
        let s4: Seq<Seq<Set<int>>> = seq![s1];
        let s5: Seq<Seq<Set<int>>> = seq![s2];
        assert(s4 =~~= s5);  // succeeds
    }

    #[verifier::ext_equal]  // necessary for invoking =~= on the struct
    struct Bar {
        a: spec_fn(int) -> int,
    }

    proof fn ext_equal_fnspec(n: int) {
        // basic case
        let f1 = (|i: int| i + 1);
        let f2 = (|i: int| 1 + i);
        assert(f1 =~= f2);  // succeeds
        // struct case
        let b1 = Bar { a: |i: int| if i == 1 { i } else { 1 } };
        let b2 = Bar { a: |i: int| 1int };
        assert(b1 =~= b2);  // succeeds
        // nested case
        let i1 = (|i: int| i + 2);
        let i2 = (|i: int| 2 + i);
        let n1: Seq<spec_fn(int) -> int> = seq![i1];
        let n2: Seq<spec_fn(int) -> int> = seq![i2];
        // assert(n1 =~= n2); // FAILS
        assert(n1 =~~= n2);  // succeeds
    }
}
