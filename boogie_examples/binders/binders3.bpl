function f<T1,T2>(x: T1, y: T2) : int;

function g<T>(x: <T1>[T1]T) : <T3>[T3]T;

function q(x: int) : int;

const C: int;
var G: int;

axiom C > 0;

//axioms can refer to constants
axiom (forall <T1> x: T1 :: f(x, C) > 0);

procedure p() returns ()
{
    var z: int;
    var m: [int]int;
    var m2: [int]([int]int);
    var m3: <T> [T] T;

    assume (forall x: int :: q(x) != 0);

    assume (forall <T2> i1: int, i2: T2 :: i1 > 0 ==> f(i1,i2)+ f(i2,i1) > 0);
    assume (forall x: int :: x > 0 ==> f(x,C)+f(x,G)+f(x,z) > 0);
    assert f(1,C)+f(1,G)+f(1,z) > 0;
}