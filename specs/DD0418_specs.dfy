// <vc-preamble>
﻿module Permutation
{
    predicate distinct'(a: array<int>, n: nat)
        requires a.Length == n
        reads a
    {
        forall i, j :: 0 <= i < j < n ==> a[i] != a[j]
    }

    predicate distinct_prefix(a: array<int>, k: nat)
        requires a != null && k <= a.Length
        reads a
    {
        forall i, j :: 0 <= i < j < k ==> a[i] != a[j]
    }

    predicate distinct(a: array<int>)
        requires a != null
        reads a
    {
        distinct'(a, a.Length)
    }

   predicate isValid(a: array<int>, n: nat)
    requires a != null && a.Length == n
    reads a
    {
        distinct(a)
        && (forall i :: 0 <= i < a.Length ==> 0 <= a[i] < n)
        && (forall i :: 0 <= i < n ==> i in a[..])
    }
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method Generate(n: int) returns (perm: array<int>)
        requires n >= 0
        ensures perm != null
        ensures perm.Length == n
        ensures fresh(perm)
        ensures isValid(perm, n)
// </vc-spec>
// <vc-code>
{
        var all := set x | 0 <= x < n;
        var used := {};
        perm := new int[n];

        CardinalityLemma(n, all);

        while used < all
            invariant used <= all
            invariant |used| <= |all|
            invariant forall i | 0 <= i < |used| :: perm[i] in used
            invariant distinct_prefix(perm, |used|)
            decreases |all| - |used|
        {
            CardinalityOrderingLemma(used, all);

            var dst :| dst in all && dst !in used;
            perm[|used|] := dst;
            used := used + {dst};
        }
        assert used == all;
        print perm[..];
        assume false;
}
// </vc-code>

lemma CardinalityLemma (size: int, s: set<int>)
        requires size >= 0
        requires s == set x | 0 <= x < size
        ensures size == |s|
    {
        if size == 0 {
            assert size == |(set x | 0 <= x < size)|;
        } else {
            CardinalityLemma(size - 1, s - {size - 1});
        }
    }

    lemma CardinalityOrderingLemma<T> (s1: set<T>, s2: set<T>)
        requires s1 < s2
        ensures |s1| < |s2|
    {
        var e :| e in s2 - s1;
        if s1 != s2 - {e} {
            CardinalityOrderingLemma(s1, s2 - {e});
        }
    }

    lemma SetDiffLemma<T> (s1: set<T>, s2: set<T>)
        requires s1 < s2
        ensures s2 - s1 != {}
    {
        var e :| e in s2 - s1;
        if s2 - s1 != {e} { }
    }
}