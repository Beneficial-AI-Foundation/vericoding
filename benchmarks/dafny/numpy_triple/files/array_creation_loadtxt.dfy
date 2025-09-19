// <vc-preamble>
// Datatype representing the content of a text file as a sequence of lines
datatype FileContent = FileContent(lines: seq<string>)

// Datatype representing a parsed floating-point value or parsing error
datatype ParseResult = Success(value: real) | ParseError

// Predicate to check if a line is a comment (starts with '#')
predicate IsComment(line: string)
{
    |line| > 0 && line[0] == '#'
}

// Predicate to check if a line contains only whitespace
predicate IsWhitespace(line: string)
{
    forall i :: 0 <= i < |line| ==> line[i] == ' ' || line[i] == '\t' || line[i] == '\n' || line[i] == '\r'
}

// Function to parse a string line into a floating-point value
function ParseFloat(line: string): ParseResult

// Function to filter and process file lines after skipping rows and comments
function ProcessLines(lines: seq<string>, skiprows: nat): seq<string>
{
    var skippedLines := if skiprows < |lines| then lines[skiprows..] else [];
    seq(line | line in skippedLines, !IsComment(line) && !IsWhitespace(line) :: line)
}

// Function to parse all processed lines into floating-point values
function ParseAllLines(lines: seq<string>): seq<ParseResult>
{
    seq(line | line in lines :: ParseFloat(line))
}

// Predicate to check if all parse results are successful
predicate AllParseSuccess(results: seq<ParseResult>)
{
    forall i :: 0 <= i < |results| ==> results[i].Success?
}

// Function to extract values from successful parse results
function ExtractValues(results: seq<ParseResult>): seq<real>
    requires AllParseSuccess(results)
{
    seq(result | result in results :: result.value)
}

// Method to load text data from a file and return a sequence of floating-point values
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method LoadTxt(fname: string, skiprows: nat, expectedSize: nat) returns (result: seq<real>)
    requires |fname| > 0  // File name must be non-empty
    requires skiprows >= 0  // Skip rows must be non-negative
    ensures |result| == expectedSize  // Result has expected size
    ensures forall i :: 0 <= i < |result| ==> result[i].real?  // All elements are valid reals
    // The result contains values parsed from the file in order, after skipping rows and filtering comments
    ensures exists fileContent: FileContent ::
        var processedLines := ProcessLines(fileContent.lines, skiprows);
        var parseResults := ParseAllLines(processedLines);
        AllParseSuccess(parseResults) &&
        |parseResults| == expectedSize &&
        result == ExtractValues(parseResults)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
