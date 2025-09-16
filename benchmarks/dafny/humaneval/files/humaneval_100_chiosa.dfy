// <vc-preamble>
// ======= TASK =======
// Given a positive integer n, create a pile with n levels of stones where the first level
// contains n stones and each subsequent level contains the next number of the same parity
// (odd/even) as n. Return a sequence representing the number of stones in each level.

// ======= SPEC REQUIREMENTS =======
predicate ValidInput(n: int)
{
    n > 0
}

predicate ValidPile(pile: seq<int>, n: int)
{
    && |pile| == n
    && (n > 0 ==> |pile| > 0 && pile[0] == n)
    && (forall i :: 0 <= i < |pile| ==> pile[i] == n + 2 * i)
    && (forall i :: 0 <= i < |pile| - 1 ==> pile[i+1] == pile[i] + 2)
}
// </vc-preamble>

// <vc-helpers>
// ======= HELPERS =======
// </vc-helpers>

// <vc-spec>
// ======= MAIN METHOD =======
method make_a_pile(n: int) returns (pile: seq<int>)
    requires ValidInput(n)
    ensures ValidPile(pile, n)
// </vc-spec>
// <vc-code>
{
    pile := [];
    var current_stones := n;
    var i := 0;

    while i < n
        invariant 0 <= i <= n
        invariant |pile| == i
        invariant current_stones == n + 2 * i
        invariant forall j :: 0 <= j < i ==> pile[j] == n + 2 * j
    {
        pile := pile + [current_stones];
        current_stones := current_stones + 2;
        i := i + 1;
    }
}
// </vc-code>
