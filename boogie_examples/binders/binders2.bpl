function f<T1,T2>(x: T1, y: T2) : int;

procedure p() returns ()
{
    var b: bool;
    var c: bool;
    var m: [int]int;
    var m2: [int]([int]int);
    var m3: <T> [T] T;

    m := (lambda x: int :: x+1);
    m2 := (lambda x: int :: (lambda y: int :: y+x));

    assume (forall <T2> i1: int, i2: T2 :: i1 > 0 ==> f(i1,i2)+ f(i2,i1) > 0);

    assume (forall <T2> :: (forall  i1: int, i2: T2 :: i1 > 0 ==> f(i1,i2)+ f(i2,i1) > 0));

    
    assume (forall x: int :: x > 0 ==> f(x,x) > 0);
}