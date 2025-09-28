// <vc-preamble>

function count_upper(s: string): int
{
    if |s| == 0 then 0
    else (if 'A' <= s[0] <= 'Z' then 1 else 0) + count_upper(s[1..])
}

function count_lower(s: string): int
{
    if |s| == 0 then 0
    else (if 'a' <= s[0] <= 'z' then 1 else 0) + count_lower(s[1..])
}

function strength(s: string): int
{
    count_upper(s) - count_lower(s)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): transitivity of > and >= */
lemma GreaterTransitive(a: int, b: int, c: int)
  requires a > b
  requires b >= c
  ensures a > c
{
  calc {
    a;
    > b;
    >= c;
  }
}

// </vc-helpers>

// <vc-spec>
method Strongest_Extension(class_name: string, extensions: seq<string>) returns (result: string)
    requires |extensions| > 0
    ensures exists i :: (0 <= i < |extensions| && result == class_name + "." + extensions[i] &&
            (forall j :: 0 <= j < |extensions| ==> strength(extensions[i]) >= strength(extensions[j])) &&
            (forall j :: 0 <= j < i ==> strength(extensions[j]) < strength(extensions[i])))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): maintain invariants and call helper to propagate comparison */
  var n := |extensions|;
  var best := 0;
  var bestStrength := strength(extensions[0]);
  var i := 1;
  while i < n
    invariant n > 0
    invariant 0 <= best && best < n
    invariant 1 <= i && i <= n
    invariant best < i
    invariant forall j :: 0 <= j < i ==> strength(extensions[best]) >= strength(extensions[j])
    invariant forall j :: 0 <= j < best ==> strength(extensions[j]) < strength(extensions[best])
    invariant bestStrength == strength(extensions[best])
    decreases n - i
  {
    var s := strength(extensions[i]);
    var oldBest := best;
    var oldBestStrength := bestStrength;
    if s > oldBestStrength {
      var k := 0;
      while k < i
        invariant 0 <= k && k <= i
      {
        assert strength(extensions[oldBest]) >= strength(extensions[k]);
        assert oldBestStrength == strength(extensions[oldBest]);
        assert oldBestStrength >= strength(extensions[k]);
        GreaterTransitive(s, oldBestStrength, strength(extensions[k]));
        k := k + 1;
      }
      best := i;
      bestStrength := s;
    }
    i := i + 1;
  }
  result := class_name + "." + extensions[best];
}

// </vc-code>
