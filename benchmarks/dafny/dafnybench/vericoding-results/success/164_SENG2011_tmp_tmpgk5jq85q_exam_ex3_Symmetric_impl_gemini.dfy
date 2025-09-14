// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Symmetric(a: array<int>) returns (flag: bool)
ensures flag == true ==> forall x :: 0 <= x < a.Length ==> a[x] == a[a.Length - x - 1]
ensures flag == false ==> exists x :: 0 <= x < a.Length && a[x] != a[a.Length - x - 1]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): [added proof block to establish full symmetry from loop invariant] */
  flag := true;
  var i := 0;
  while i < a.Length / 2
    invariant 0 <= i <= a.Length / 2
    invariant flag ==> (forall k :: 0 <= k < i ==> a[k] == a[a.Length - 1 - k])
  {
    if a[i] != a[a.Length - 1 - i] {
      flag := false;
      return;
    }
    i := i + 1;
  }

  if flag {
    forall k | 0 <= k < a.Length
      ensures a[k] == a[a.Length - 1 - k]
    {
      if k >= a.Length / 2 {
        var j := a.Length - 1 - k;
        if j < i { 
          assert a[j] == a[a.Length - 1 - j];
        }
      }
    }
  }
}
// </vc-code>
