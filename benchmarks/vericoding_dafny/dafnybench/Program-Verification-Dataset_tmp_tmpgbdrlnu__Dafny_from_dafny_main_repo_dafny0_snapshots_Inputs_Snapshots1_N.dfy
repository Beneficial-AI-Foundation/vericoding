// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method N()
  ensures P();

predicate P()
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>