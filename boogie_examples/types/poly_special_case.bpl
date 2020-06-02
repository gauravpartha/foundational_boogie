type MyType _ _;

//B
function f1<A,B> (x: MyType A B) returns (B);

function f2<A,B> (x: MyType bool B) returns (MyType B A);

procedure m() {
    var c1: MyType bool int;
    var c2: MyType int int;

    assume f1(c1) > 0;
    assert f1(c1) >= 0;

    assume c2 != f2(c1);
    assert c2 != f2(c1);
}