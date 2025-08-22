// RUN: %dafny  /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

//IMPL 
// RUN: %dafny  /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
}

//IMPL 
// The verification of the following methods requires knowledge
// about the injectivity of sequence displays.

method M0()
{
}

//IMPL 

method M1()
{
}

//IMPL 

method EqualityOfStrings0() {
}

//IMPL 

method EqualityOfStrings1() {
}

//ATOM_PLACEHOLDER_M2

//ATOM_PLACEHOLDER_M3