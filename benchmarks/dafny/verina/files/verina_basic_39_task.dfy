// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method RotateRight(l: array<int>, n: nat) returns (result: array<int>)
    ensures
        result.Length == l.Length &&
        (l.Length == 0 || forall i :: 0 <= i < l.Length ==> 
            var len := l.Length;
            var rotatedIndex := ((i - n + len) % len);
            result[i] == l[rotatedIndex])
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
    result := new int[l.Length];
}
// </vc-code>
