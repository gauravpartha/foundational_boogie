function f(x: int) : int;

procedure p() returns ()
{
    var x: int;
    var b: bool;
    var c: bool;

    assume (forall y: int :: y > x ==> f(y) > 0);

    b := (forall y: int :: y > x ==> f(y) > 0);

    assume (forall i1: int, i2: int :: i1 + i2 > 0 ==> f(i1)+ f(i2) > 0);
}