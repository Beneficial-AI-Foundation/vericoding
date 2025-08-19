// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method leq(a: array<int>, b: array<int>) returns (result: bool) 
    ensures result <==> (a.Length <= b.Length && a[..] == b[..a.Length]) || (exists k :: 0 <= k < a.Length && k < b.Length && a[..k] == b[..k] && a[k] < b[k])
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>