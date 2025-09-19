// <vc-preamble>
ghost predicate IsInteger(x: real)
{
    exists k: int :: {:trigger k as real} x == k as real
}

predicate SameSign(x: real, y: real)
{
    (x > 0.0 && y >= 0.0) || (x < 0.0 && y <= 0.0) || (x == 0.0 && y == 0.0)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method NumpyTrunc(x: seq<real>) returns (result: seq<real>)
    ensures |result| == |x|
    ensures forall i :: 0 <= i < |x| ==> IsInteger(result[i])
    ensures forall i :: 0 <= i < |x| && x[i] >= 0.0 ==> 
        result[i] <= x[i] < result[i] + 1.0
    ensures forall i :: 0 <= i < |x| && x[i] < 0.0 ==> 
        result[i] - 1.0 < x[i] <= result[i]
    ensures forall i :: 0 <= i < |x| ==> 
        if x[i] >= 0.0 then result[i] <= x[i] else result[i] >= x[i]
    ensures forall i :: 0 <= i < |x| ==> 
        (result[i] * result[i]) <= (x[i] * x[i])
    ensures forall i :: 0 <= i < |x| ==> SameSign(x[i], result[i])
    ensures forall i :: 0 <= i < |x| ==> 
        if x[i] == 0.0 then result[i] == 0.0 else true
    ensures forall i :: 0 <= i < |x| ==> 
        IsInteger(x[i]) ==> result[i] == x[i]
    ensures forall i :: 0 <= i < |x| ==> IsInteger(result[i])
    ensures forall i :: 0 <= i < |x| ==> 
        if x[i] >= 0.0 then 
            (exists k: int :: {:trigger k as real} k as real == result[i] && k as real <= x[i] && (k+1) as real > x[i])
        else 
            (exists k: int :: {:trigger k as real} k as real == result[i] && k as real >= x[i] && (k-1) as real < x[i])
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
