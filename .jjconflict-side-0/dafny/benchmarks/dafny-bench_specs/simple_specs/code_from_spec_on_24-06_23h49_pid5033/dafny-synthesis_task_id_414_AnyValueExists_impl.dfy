//IMPL 
method AnyValueExists(seq1: seq<int>, seq2: seq<int>) returns (result: bool)
  ensures result <==> (exists i :: 0 <= i < |seq1| && seq1[i] in seq2)
{
  result := false;
  var index := 0;
  
  while index < |seq1|
    invariant 0 <= index <= |seq1|
    invariant result <==> (exists i :: 0 <= i < index && seq1[i] in seq2)
  {
    if seq1[index] in seq2 {
      result := true;
      return;
    }
    index := index + 1;
  }
}