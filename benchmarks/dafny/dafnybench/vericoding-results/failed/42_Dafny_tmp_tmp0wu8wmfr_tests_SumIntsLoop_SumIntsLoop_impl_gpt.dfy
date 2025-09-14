function sumInts( n: int ): int
    requires n >= 0;
{
    if n == 0 then
        0
    else
        sumInts(n-1)+n
}

// <vc-helpers>
lemma SumIntsStep(k: int)
  requires k > 0
  ensures sumInts(k) == sumInts(k-1) + k
{
  calc {
    sumInts(k);
    == { }
    (if k == 0 then 0 else sumInts(k-1) + k);
    == { assert k != 0 }
    sumInts(k-1) + k;
  }
}
// </vc-helpers>

// <vc-spec>
method SumIntsLoop( n: int ) returns ( s: int )
    requires n >= 0;
    ensures s == sumInts(n)
    ensures s == n*(n+1)/2;
// </vc-spec>
// <vc-code>
{
  var i := 0;
  s := 0;
  while i < n
    invariant 0 <= i <= n
    invariant s == sumInts(i)
    invariant 2*s == i*(i+1)
    decreases n - i
  {
    var oldI := i;
    var oldS := s;
    i := i + 1;
    s := oldS + i;

    assert i > 0;
    assert i - 1 == oldI;
    calc {
      s;
      == { }
      oldS + i;
      == { assert oldS == sumInts(oldI) }
      sumInts(oldI) + i;
      == { assert i - 1 == oldI }
      sumInts(i-1) + i;
      == { SumIntsStep(i) }
      sumInts(i);
    }

    calc {
      2*s;
      == { }
      2*(oldS + i);
      == { }
      2*oldS + 2*i;
      == { assert 2*oldS == oldI*(oldI+1) }
      oldI*(oldI+1) + 2*i;
      == { assert i == oldI + 1 }
      oldI*(oldI+1) + 2*(oldI+1);
      == { }
      (oldI+1)*(oldI+2);
      == { assert i == oldI + 1 }
      i*(i+1);
    }
  }

  assert i == n;
  assert s == sumInts(n);

  assert 2*s == n*(n+1);
  assert (2*s)/2 == s;
  calc {
    s;
    == { }
    (2*s)/2;
    == { assert 2*s == n*(n+1) }
    (n*(n+1))/2;
  }
}
// </vc-code>

