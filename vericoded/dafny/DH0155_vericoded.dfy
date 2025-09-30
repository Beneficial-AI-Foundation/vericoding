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
  var max_strength := strength(extensions[0]);
  var max_index := 0;
  
  var i := 1;
  while i < |extensions|
    invariant 1 <= i <= |extensions|
    invariant 0 <= max_index < |extensions|
    invariant max_strength == strength(extensions[max_index])
    invariant forall j :: 0 <= j < i ==> strength(extensions[j]) <= max_strength
    invariant forall j :: 0 <= j < max_index ==> strength(extensions[j]) < strength(extensions[max_index])
    invariant forall j :: max_index < j < i ==> strength(extensions[j]) <= strength(extensions[max_index])
  {
    if strength(extensions[i]) > max_strength {
      max_strength := strength(extensions[i]);
      max_index := i;
    }
    i := i + 1;
  }
  
  result := class_name + "." + extensions[max_index];
}
// </vc-code>
