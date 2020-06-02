var i: int;
var j: int;

procedure swap() returns ()
    ensures i == old(j);
    ensures j == old(i);
    modifies i, j;
{
    i,j := j,i;
}