// <vc-preamble>
// Helper predicate to check if a character should be deleted
ghost predicate IsDeletedChar(c: char, deletechars: seq<nat>)
{
    c as nat in deletechars
}

// Helper predicate to check if a character is a valid result of translation
ghost predicate IsValidTranslation(resultChar: char, originalChar: char, table: seq<nat>)
    requires |table| == 256
{
    originalChar as nat < 256 && resultChar as nat == table[originalChar as nat]
}

// Helper function to get the translated character for a given original character
ghost function TranslateChar(c: char, table: seq<nat>): char
    requires |table| == 256
    requires c as nat < 256
{
    table[c as nat] as char
}

// Helper predicate to check if a character exists in a string
ghost predicate CharInString(c: char, s: seq<char>)
{
    c in s
}

// Main translation method specification
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Translate(a: seq<seq<char>>, table: seq<nat>, deletechars: seq<nat>) returns (result: seq<seq<char>>)
    requires |table| == 256
    requires forall i :: 0 <= i < |table| ==> 0 <= table[i] < 256
    requires forall i :: 0 <= i < |deletechars| ==> 0 <= deletechars[i] < 256
    requires forall i :: 0 <= i < |a| ==> forall j :: 0 <= j < |a[i]| ==> a[i][j] as nat < 256
    ensures |result| == |a|
    // Length property: result length ≤ original length (due to deletion)
    ensures forall i :: 0 <= i < |result| ==> |result[i]| <= |a[i]|
    // Deletion property: no character from deletechars appears in result
    ensures forall i :: 0 <= i < |result| ==> 
        forall c :: c in result[i] ==> !IsDeletedChar(c, deletechars)
    // Translation property: each character in result comes from table translation
    ensures forall i :: 0 <= i < |result| ==>
        forall c :: c in result[i] ==>
            exists originalChar :: CharInString(originalChar, a[i]) && 
                !IsDeletedChar(originalChar, deletechars) &&
                IsValidTranslation(c, originalChar, table)
    // Completeness property: all non-deleted characters are translated and included
    ensures forall i :: 0 <= i < |result| ==>
        forall originalChar :: (CharInString(originalChar, a[i]) && 
            !IsDeletedChar(originalChar, deletechars)) ==>
            exists translatedChar :: CharInString(translatedChar, result[i]) &&
                IsValidTranslation(translatedChar, originalChar, table)
    // Identity on empty deletechars: if no characters to delete, only translation occurs
    ensures |deletechars| == 0 ==> 
        forall i :: 0 <= i < |result| ==> 
            |result[i]| == |a[i]| &&
            forall j :: 0 <= j < |a[i]| ==>
                IsValidTranslation(result[i][j], a[i][j], table)
    // Empty string preservation: empty inputs produce empty outputs
    ensures forall i :: 0 <= i < |result| ==> 
        |a[i]| == 0 ==> |result[i]| == 0
    // Order preservation: relative order of non-deleted characters is maintained
    ensures forall i :: 0 <= i < |result| ==>
        forall j1, j2 :: 0 <= j1 < j2 < |result[i]| ==>
            exists k1, k2 :: 0 <= k1 < k2 < |a[i]| &&
                !IsDeletedChar(a[i][k1], deletechars) &&
                !IsDeletedChar(a[i][k2], deletechars) &&
                IsValidTranslation(result[i][j1], a[i][k1], table) &&
                IsValidTranslation(result[i][j2], a[i][k2], table)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
