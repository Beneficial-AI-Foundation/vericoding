

// <vc-helpers>
lemma {:vcs_split_on_every_assert} Rot2VowelProperty(c: char)
  requires is_vowel(c)
  ensures is_vowel(rot2(c))
{
  match c {
    case 'a' => assert rot2(c) == 'c';
    case 'e' => assert rot2(c) == 'g';
    case 'i' => assert rot2(c) == 'k';
    case 'o' => assert rot2(c) == 'q';
    case 'u' => assert rot2(c) == 'w';
    case 'A' => assert rot2(c) == 'C';
    case 'E' => assert rot2(c) == 'G';
    case 'I' => assert rot2(c) == 'K';
    case 'O' => assert rot2(c) == 'Q';
    case 'U' => assert rot2(c) == 'W';
  }
}

function swap_case(c: char): char
  requires 'a' <= c <= 'z' || 'A' <= c <= 'Z'
  ensures 'a' <= c <= 'z' ==> 'A' <= swap_case(c) <= 'Z'
  ensures 'A' <= c <= 'Z' ==> 'a' <= swap_case(c) <= 'z'
  ensures is_vowel(swap_case(c)) == is_vowel(c)
{
  if 'a' <= c <= 'z' then
    'A' + (c - 'a')
  else
    'a' + (c - 'A')
}

function rot2(c: char): char
  requires is_vowel(c)
{
    match c {
      case 'a' => 'c'
      case 'e' => 'g'
      case 'i' => 'k'
      case 'o' => 'q'
      case 'u' => 'w'
      case 'A' => 'C'
      case 'E' => 'G'
      case 'I' => 'K'
      case 'O' => 'Q'
      case 'U' => 'W'
    }
}

function is_vowel(c: char) : bool {
    (c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u')
    || (c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U')
}
// </vc-helpers>

// <vc-spec>
method encode(s: string) returns (t: string)
  // pre-conditions-start
  requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z' || 'A' <= s[i] <= 'Z'
  // pre-conditions-end
  // post-conditions-start
  ensures |s| == |t|
  ensures forall i :: 0 <= i < |s| && is_vowel(s[i]) ==> t[i] == rot2(swap_case(s[i]))
  ensures forall i :: 0 <= i < |s| && !is_vowel(s[i]) ==> t[i] == swap_case(s[i])
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var chars := new char[|s|];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant chars.Length == |s|
    invariant forall j :: 0 <= j < i && is_vowel(s[j]) ==> chars[j] == rot2(swap_case(s[j]))
    invariant forall j :: 0 <= j < i && !is_vowel(s[j]) ==> chars[j] == swap_case(s[j])
  {
    if is_vowel(s[i]) {
      chars[i] := rot2(swap_case(s[i]));
    } else {
      chars[i] := swap_case(s[i]);
    }
    i := i + 1;
  }
  t := new string(chars);
}
// </vc-code>

function swap_case(c: char): char
  // pre-conditions-start
  requires 'a' <= c <= 'z' || 'A' <= c <= 'Z'
  // pre-conditions-end
  // post-conditions-start
  ensures 'a' <= c <= 'z' ==> 'A' <= swap_case(c) <= 'Z'
  ensures 'A' <= c <= 'Z' ==> 'a' <= swap_case(c) <= 'z'
  ensures is_vowel(swap_case(c)) == is_vowel(c)
  // post-conditions-end
{
  // impl-start
  if 'a' <= c <= 'z' then
    'A' + (c - 'a')
  else
    'a' + (c - 'A')
  // impl-end
}
// pure-end
function rot2(c: char): char
  requires is_vowel(c)
{
    (c as int + 2) as char
}
// pure-end
function is_vowel(c: char) : bool {
    (c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u')
    || (c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U')
}
// pure-end