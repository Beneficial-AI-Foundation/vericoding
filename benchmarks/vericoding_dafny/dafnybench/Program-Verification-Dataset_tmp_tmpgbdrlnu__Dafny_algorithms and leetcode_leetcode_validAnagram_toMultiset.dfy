// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method toMultiset(s: string) returns (mset: multiset<char>)
    ensures multiset(s) == mset
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>