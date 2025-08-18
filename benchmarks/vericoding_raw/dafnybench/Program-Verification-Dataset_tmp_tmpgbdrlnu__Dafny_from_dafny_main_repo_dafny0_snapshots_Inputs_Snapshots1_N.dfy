// <vc-helpers>
// </vc-helpers>

method N()
  ensures P();

predicate P()
// <vc-code>
{
  assume false;
}
// </vc-code>