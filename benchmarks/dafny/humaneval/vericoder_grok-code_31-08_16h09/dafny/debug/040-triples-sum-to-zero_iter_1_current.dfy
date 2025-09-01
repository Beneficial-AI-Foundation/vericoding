

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method triples_sum_to_zero(l : seq<int>) returns (result : bool)
    // post-conditions-start
    ensures result ==> exists i : int, j : int, k : int :: 0 <= i < |l| && 0 <= j < |l| && 0 <= k < |l| && i != j && j != k && i != k && l[i] + l[j] + l[k] == 0
    ensures !result ==> forall i : int, j : int, k : int :: 0 <= i < |l| && 0 <= j < |l| && 0 <= k < |l| && i != j && j != k && i != k ==> l[i] + l[j] + l[k] != 0
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var n := |l|;
  var i := 0;
  while i < n {
    var j := i + 1;
    while j < n {
      var k := j + 1;
      while k < n {
        if l[i] + l[j] + l[k] == 0 {
          return true;
        }
        k := k + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  return false;
}
// </vc-code>

