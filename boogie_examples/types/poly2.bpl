type Foo A; 

function f<A>(x: A) returns (bool); /* type parameter */

procedure  m<T>(y: T) returns () {

    var x: bool;
    var a: Foo int;
    var b: Foo bool;

    x := f(0) ==> f(y);

    assert a != b;
}