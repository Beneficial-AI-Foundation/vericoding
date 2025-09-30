// <vc-preamble>

datatype SplitResult = StringSeq(words: seq<string>) | Count(value: int)

function contains_space(txt: string): bool
{
    exists i :: 0 <= i < |txt| && txt[i] == ' '
}

function contains_comma(txt: string): bool
{
    exists i :: 0 <= i < |txt| && txt[i] == ','
}
function split_on_whitespace(txt: string): seq<string>
    ensures forall w :: w in split_on_whitespace(txt) ==> |w| > 0
    ensures forall w :: w in split_on_whitespace(txt) ==> forall c :: c in w ==> c != ' '
    decreases |txt|
{
    if |txt| == 0 then
        []
    else
        split_on_whitespace_helper(txt, 0, [], "")
}

function split_on_whitespace_helper(txt: string, i: int, result: seq<string>, current_word: string): seq<string>
    requires 0 <= i <= |txt|
    requires forall w :: w in result ==> |w| > 0
    requires forall w :: w in result ==> forall c :: c in w ==> c != ' '
    requires forall c :: c in current_word ==> c != ' '
    ensures forall w :: w in split_on_whitespace_helper(txt, i, result, current_word) ==> |w| > 0
    ensures forall w :: w in split_on_whitespace_helper(txt, i, result, current_word) ==> forall c :: c in w ==> c != ' '
    decreases |txt| - i
{
    if i == |txt| then
        if |current_word| > 0 then
            result + [current_word]
        else
            result
    else if txt[i] == ' ' then
        if |current_word| > 0 then
            split_on_whitespace_helper(txt, i + 1, result + [current_word], "")
        else
            split_on_whitespace_helper(txt, i + 1, result, "")
    else
        split_on_whitespace_helper(txt, i + 1, result, current_word + [txt[i]])
}

function split_on_comma(txt: string): seq<string>
    ensures |split_on_comma(txt)| > 0
    decreases |txt|
{
    if |txt| == 0 then
        [""]
    else
        split_on_comma_helper(txt, 0, [], "")
}

function split_on_comma_helper(txt: string, i: int, result: seq<string>, current_word: string): seq<string>
    requires 0 <= i <= |txt|
    ensures |split_on_comma_helper(txt, i, result, current_word)| > 0
    decreases |txt| - i
{
    if i == |txt| then
        result + [current_word]
    else if txt[i] == ',' then
        split_on_comma_helper(txt, i + 1, result + [current_word], "")
    else
        split_on_comma_helper(txt, i + 1, result, current_word + [txt[i]])
}

function count_odd_position_lowercase(txt: string): int
    ensures count_odd_position_lowercase(txt) >= 0
    ensures count_odd_position_lowercase(txt) <= |txt|
{
    count_odd_position_lowercase_helper(txt, 0)
}

function count_odd_position_lowercase_helper(txt: string, i: int): int
    requires 0 <= i <= |txt|
    ensures count_odd_position_lowercase_helper(txt, i) >= 0
    ensures count_odd_position_lowercase_helper(txt, i) <= |txt| - i
    decreases |txt| - i
{
    if i == |txt| then
        0
    else
        var c := txt[i];
        var count_rest := count_odd_position_lowercase_helper(txt, i + 1);
        if 'a' <= c <= 'z' && (c as int - 'a' as int) % 2 == 1 then
            1 + count_rest
        else
            count_rest
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method split_words(txt: string) returns (result: SplitResult)
    ensures (contains_space(txt) ==> result.StringSeq?) &&
            (!contains_space(txt) && contains_comma(txt) ==> result.StringSeq?) &&
            (!contains_space(txt) && !contains_comma(txt) ==> result.Count?)
    ensures contains_space(txt) ==> result == StringSeq(split_on_whitespace(txt))
    ensures !contains_space(txt) && contains_comma(txt) ==> result == StringSeq(split_on_comma(txt))
    ensures !contains_space(txt) && !contains_comma(txt) ==> result == Count(count_odd_position_lowercase(txt))
    ensures result.StringSeq? ==> |result.words| >= 0
    ensures result.Count? ==> result.value >= 0
    ensures contains_space(txt) ==> (forall w :: w in result.words ==> |w| > 0)
    ensures !contains_space(txt) && contains_comma(txt) ==> |result.words| > 0
// </vc-spec>
// <vc-code>
{
  if contains_space(txt) {
    result := StringSeq(split_on_whitespace(txt));
  } else if contains_comma(txt) {
    result := StringSeq(split_on_comma(txt));
  } else {
    result := Count(count_odd_position_lowercase(txt));
  }
}
// </vc-code>
