// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method flipud(m: seq<real>) returns (result: seq<real>)
    ensures |result| == |m|
    ensures forall i :: 0 <= i < |result| ==> result[i] == m[|m| - 1 - i]
// </vc-spec>
// <vc-code>
{
  result := seq(|m|, i requires 0 <= i < |m| => m[|m| - 1 - i]);
}
// </vc-code>
