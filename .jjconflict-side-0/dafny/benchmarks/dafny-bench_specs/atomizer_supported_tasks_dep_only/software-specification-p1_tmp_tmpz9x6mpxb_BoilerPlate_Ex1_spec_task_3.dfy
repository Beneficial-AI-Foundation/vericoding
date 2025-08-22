//ATOM_PLACEHOLDER_Tree//ATOM_PLACEHOLDER_Code// ATOM 

function serialise<V>(t : Tree<V>) : seq<Code<V>> 
{
  match t {
    case Leaf(v) => [ CLf(v) ]
    case SingleNode(v, t) => serialise(t) + [ CSNd(v) ]
    case DoubleNode(v, t1, t2) => serialise(t2) + serialise(t1) + [ CDNd(v) ]
  }
}


// Ex 1
//ATOM_PLACEHOLDER_deserialiseAux

//ATOM_PLACEHOLDER_deserialise

// Ex 2
//ATOM_PLACEHOLDER_testSerializeWithASingleLeaf

//ATOM_PLACEHOLDER_testSerializeNullValues

// SPEC 

method testSerializeWithAllElements()
{
}


// Ex 3 

//ATOM_PLACEHOLDER_testDeseraliseWithASingleLeaf

//ATOM_PLACEHOLDER_testDeserializeWithASingleNode

//ATOM_PLACEHOLDER_testDeserialiseWithAllElements

// Ex 4 
//ATOM_PLACEHOLDER_SerialiseLemma


//ATOM_PLACEHOLDER_DeserialisetAfterSerialiseLemma



