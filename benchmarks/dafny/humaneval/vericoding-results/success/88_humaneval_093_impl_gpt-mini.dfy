// <vc-preamble>

predicate isVowel(c: char)
{
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' ||
    c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}

function getVowelReplacement(c: char): char
    requires isVowel(c)
{
    match c
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

function swapCase(c: char): char
{
    if 'a' <= c <= 'z' then
        (c as int - 'a' as int + 'A' as int) as char
    else if 'A' <= c <= 'Z' then
        (c as int - 'A' as int + 'a' as int) as char
    else
        c
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): prove vowel replacement yields a letter */
lemma VowelReplacementIsLetter(c: char)
  requires isVowel(c)
  ensures ('a' <= getVowelReplacement(c) <= 'z') || ('A' <= getVowelReplacement(c) <= 'Z')
{
  if c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' {
    var r := getVowelReplacement(c);
    assert 'a' <= r <= 'z';
  } else {
    var r := getVowelReplacement(c);
    assert 'A' <= r <= 'Z';
  }
}

/* helper modified by LLM (iteration 3): prove swapCase maps letters to letters */
lemma SwapCaseIsLetterForAlpha(c: char)
  requires ('a' <= c <= 'z') || ('A' <= c <= 'Z')
  ensures ('a' <= swapCase(c) <= 'z') || ('A' <= swapCase(c) <= 'Z')
{
  if 'a' <= c <= 'z' {
    var d := c as int - 'a' as int;
    assert 0 <= d <= 25;
    var si := d + 'A' as int;
    var s := swapCase(c);
    assert s as int == si;
    assert 'A' as int <= si <= 'Z' as int;
    assert 'A' <= s <= 'Z';
  } else {
    var d := c as int - 'A' as int;
    assert 0 <= d <= 25;
    var si := d + 'a' as int;
    var s := swapCase(c);
    assert s as int == si;
    assert 'a' as int <= si <= 'z' as int;
    assert 'a' <= s <= 'z';
  }
}

// </vc-helpers>

// <vc-spec>
method encode(message: string) returns (result: string)
    requires forall i :: 0 <= i < |message| ==> (('a' <= message[i] <= 'z') || ('A' <= message[i] <= 'Z') || message[i] == ' ')
    ensures |result| == |message|
    ensures forall i :: 0 <= i < |message| ==> 
        if message[i] == ' ' then result[i] == ' '
        else if isVowel(message[i]) then result[i] == swapCase(getVowelReplacement(message[i]))
        else result[i] == swapCase(message[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): build result incrementally without using new string(arr) */
  result := "";
  var i := 0;
  while i < |message|
    invariant 0 <= i <= |message|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==>
      if message[j] == ' ' then result[j] == ' '
      else if isVowel(message[j]) then result[j] == swapCase(getVowelReplacement(message[j]))
      else result[j] == swapCase(message[j])
  {
    var c := message[i];
    var ch: char;
    if c == ' ' {
      ch := ' ';
    } else if isVowel(c) {
      ch := swapCase(getVowelReplacement(c));
    } else {
      ch := swapCase(c);
    }
    result := result + [ch];
    i := i + 1;
  }
}

// </vc-code>
