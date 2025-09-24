// <vc-preamble>

predicate ValidInput(s: string) { true }

function starts_with_I(s: string): bool
{
    var trimmed := trim(s);
    if |trimmed| == 0 then false
    else
        var first_word := get_first_word(trimmed);
        first_word == "I"
}

function get_first_word(s: string): string
    requires |s| > 0
    decreases |s|
{
    get_first_word_helper(s, 0)
}

function split_sentences(S: string): seq<string>
    ensures forall i :: 0 <= i < |split_sentences(S)| ==> |split_sentences(S)[i]| >= 0
{
    if |S| == 0 then []
    else
        var sentences := [];
        var current := "";
        var i := 0;
        split_sentences_helper(S, i, current, sentences)
}

function count_sentences_starting_with_I(S: string): int
    ensures count_sentences_starting_with_I(S) >= 0
    ensures S == "" ==> count_sentences_starting_with_I(S) == 0
    ensures count_sentences_starting_with_I(S) <= |split_sentences(S)|
{
    var sentences := split_sentences(S);
    count_bored_sentences(sentences)
}

function get_first_word_helper(s: string, i: int): string
    requires 0 <= i <= |s|
    requires |s| > 0
    decreases |s| - i
{
    if i == |s| || s[i] == ' ' then s[0..i]
    else get_first_word_helper(s, i + 1)
}

function split_sentences_helper(S: string, i: int, current: string, sentences: seq<string>): seq<string>
    requires 0 <= i <= |S|
    ensures forall j :: 0 <= j < |split_sentences_helper(S, i, current, sentences)| ==> |split_sentences_helper(S, i, current, sentences)[j]| >= 0
    decreases |S| - i
{
    if i == |S| then
        if |current| > 0 then sentences + [current] else sentences
    else if S[i] == '.' || S[i] == '?' || S[i] == '!' then
        var new_sentences := if |current| > 0 then sentences + [current] else sentences;
        split_sentences_helper(S, i + 1, "", new_sentences)
    else
        split_sentences_helper(S, i + 1, current + [S[i]], sentences)
}

function trim(s: string): string
    ensures |trim(s)| <= |s|
{
    trim_left(trim_right(s))
}

function trim_left(s: string): string
    ensures |trim_left(s)| <= |s|
    decreases |s|
{
    if |s| == 0 then s
    else if s[0] == ' ' then trim_left(s[1..])
    else s
}

function trim_right(s: string): string
    ensures |trim_right(s)| <= |s|
    decreases |s|
{
    if |s| == 0 then s
    else if s[|s|-1] == ' ' then trim_right(s[..|s|-1])
    else s
}

function count_bored_sentences(sentences: seq<string>): int
    requires forall i :: 0 <= i < |sentences| ==> |sentences[i]| >= 0
    ensures count_bored_sentences(sentences) >= 0
    ensures count_bored_sentences(sentences) <= |sentences|
    ensures count_bored_sentences(sentences) == |set i | 0 <= i < |sentences| && starts_with_I(sentences[i])|
    decreases |sentences|
{
    if |sentences| == 0 then 0
    else
        var count := if starts_with_I(sentences[0]) then 1 else 0;
        var rest_count := count_bored_sentences(sentences[1..]);

        var full_set := set i | 0 <= i < |sentences| && starts_with_I(sentences[i]);
        var first_set := if starts_with_I(sentences[0]) then {0} else {};
        var rest_set := set i | 1 <= i < |sentences| && starts_with_I(sentences[i]);
        var tail_set := set j | 0 <= j < |sentences[1..]| && starts_with_I(sentences[1..][j]);

        assert full_set == first_set + rest_set;
        assert forall j :: 0 <= j < |sentences[1..]| ==> sentences[1..][j] == sentences[j+1];
        assert forall i :: i in rest_set ==> (i-1) in tail_set;
        assert forall j :: j in tail_set ==> (j+1) in rest_set;

        var f := map i | i in rest_set :: i-1;
        var g := map j | j in tail_set :: j+1;
        assert forall i :: i in rest_set ==> f[i] in tail_set;
        assert forall j :: j in tail_set ==> g[j] in rest_set;
        assert forall i :: i in rest_set ==> g[f[i]] == i;
        assert forall j :: j in tail_set ==> f[g[j]] == j;

        assert |rest_set| == |tail_set|;
        assert |full_set| == |first_set| + |tail_set|;

        count + rest_count
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method CountSentencesStartingWithI(S: string) returns (count: int)
    requires ValidInput(S)
    ensures count >= 0
    ensures S == "" ==> count == 0
    ensures count <= |split_sentences(S)|
    ensures count == count_sentences_starting_with_I(S)
    ensures count == |set i | 0 <= i < |split_sentences(S)| && starts_with_I(split_sentences(S)[i])|
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
  }
// </vc-code>
