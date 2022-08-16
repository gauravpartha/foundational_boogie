var a : int;
var b : bool;

function f(a : int) : bool;
function g(b : bool) : bool;

procedure p(x : int) {
    assume f(a);
    assume g(b);

    assert f(a);
    assert g(b); 
}