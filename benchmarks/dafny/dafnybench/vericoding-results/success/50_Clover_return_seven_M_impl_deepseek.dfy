

// <vc-helpers>
lemma SevenLemma()
ensures 7 == 7
{
}
// </vc-helpers>

// <vc-spec>
method M(x: int) returns (seven: int)
  ensures seven==7
// </vc-spec>
// <vc-code>
{
  seven := 7;
  SevenLemma();
}
// </vc-code>

