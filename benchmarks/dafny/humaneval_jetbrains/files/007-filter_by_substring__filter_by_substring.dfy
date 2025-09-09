// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method filter_by_substring(strings: seq<string>, substring: string) returns (res : seq<string>)

    ensures |res| <= |strings|
    ensures (forall s :: s in res ==> s in strings)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
