// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method LaguerreMul(c1: seq<real>, c2: seq<real>) returns (result: seq<real>)
  requires |c1| > 0
  requires |c2| > 0
  ensures |result| == |c1| + |c2| - 1
  ensures forall i :: 0 <= i < |result| ==> 
    (result[i] != 0.0 ==> 
      exists j, k :: 0 <= j < |c1| && 0 <= k < |c2| && 
        j + k == i && c1[j] != 0.0 && c2[k] != 0.0)
// </vc-spec>
// <vc-code>
{
  var n1 := |c1|;
  var n2 := |c2|;
  result := seq(n1 + n2 - 1, i => 0.0);

  var j := 0;
  while j < n1
    invariant 0 <= j <= n1
    invariant |result| == n1 + n2 - 1
    invariant forall i :: 0 <= i < |result| ==> (result[i] != 0.0 ==> 
      exists j_prime, k_prime :: 0 <= j_prime < j && 0 <= k_prime < n2 && j_prime + k_prime == i && c1[j_prime] != 0.0 && c2[k_prime] != 0.0)
  {
    var k := 0;
    while k < n2
      invariant 0 <= k <= n2
      invariant |result| == n1 + n2 - 1
      invariant forall i :: 0 <= i < |result| ==> (result[i] != 0.0 ==> 
        (exists j_prime, k_prime :: 0 <= j_prime < j && 0 <= k_prime < n2 && j_prime + k_prime == i && c1[j_prime] != 0.0 && c2[k_prime] != 0.0) ||
        (c1[j] != 0.0 && exists k_prime :: 0 <= k_prime < k && j + k_prime == i && c2[k_prime] != 0.0))
    {
      if c1[j] != 0.0 && c2[k] != 0.0 {
        var i := j + k;
        result := result[i := result[i] + c1[j] * c2[k]];
      }
      k := k + 1;
    }
    j := j + 1;
  }
}
// </vc-code>
