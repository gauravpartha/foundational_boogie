const pos: int;

var neg: int;

axiom pos > 0;

procedure p() returns ()  
  modifies neg; 
  //if this is commented, then there is an error,
  //since Boogie just does a syntactic and not an
  //semantic check on whether a global variable is modified
{
    assume pos < 0;
    assert false;
    neg := 4; 
}