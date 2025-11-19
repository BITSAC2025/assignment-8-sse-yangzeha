/**
 * verify.cpp
 * @author kisslune 
 */

#include "Z3Mgr.h"

using namespace z3;
using namespace SVF;


/* A simple example

int main() {
    int* p;
    int q;
    int* r;
    int x;

    p = malloc();
    q = 5;
    *p = q;
    x = *p;
    assert(x==5);
}
*/
void Z3Tests::test0()
{
    //  int* p;
    expr p = getZ3Expr("p");
    //  int q;
    expr q = getZ3Expr("q");
    //  int* r;
    expr r = getZ3Expr("r");
    //  int x;
    expr x = getZ3Expr("x");
    //  p = malloc();
    addToSolver(p == getMemObjAddress("malloc"));
    //  q = 5;
    addToSolver(q == 5);
    //  *p = q;
    storeValue(p, q);
    //  x = *p;
    addToSolver(x == loadValue(p));

    // print the expression values
    printExprValues();

    addToSolver(x == getZ3Expr(10));
    // print the result of satisfiability check
    std::cout << solver.check() << std::endl;
}


/*
// Simple integers

    int main() {
        int a;
        int b;
        a = 0;
        b = a + 1;
        assert(b > 0);
    }
*/
void Z3Tests::test1()
{
    /// TODO: your code starts from here
    expr a = getZ3Expr("a");
    expr b = getZ3Expr("b");

    addToSolver(a == 0);
    addToSolver(b == a + 1);

    printExprValues();
    addToSolver(b > 0);
    std::cout << solver.check() << std::endl;
}

/*
  // One-level pointers

    int main() {
        int* p;
        int q;
        int b;
        p = malloc;
        *p = 0;
        q = *p;
        *p = 3;
        b = *p + 1;
        assert(b > 3);
    }
*/
void Z3Tests::test2()
{
    /// TODO: your code starts from here
    expr p = getZ3Expr("p");
    expr q = getZ3Expr("q");
    expr b = getZ3Expr("b");

    addToSolver(p == getMemObjAddress("malloc"));
    storeValue(p, getZ3Expr(0));
    addToSolver(q == loadValue(p));
    storeValue(p, getZ3Expr(3));
    addToSolver(b == loadValue(p) + 1);

    printExprValues();
    addToSolver(b > 3);
    std::cout << solver.check() << std::endl;
}

/*
    // Mutiple-level pointers

    int main() {
        int** p;
        int* q;
        int* r;
        int x;

        p = malloc1(..);
        q = malloc2(..);
        *p = q;
        *q = 10;
        r = *p;
        x = *r;
        assert(x==10);
    }
*/
void Z3Tests::test3()
{
    /// TODO: your code starts from here
    expr p = getZ3Expr("p");
    expr q = getZ3Expr("q");
    expr r = getZ3Expr("r");
    expr x = getZ3Expr("x");

    addToSolver(p == getMemObjAddress("malloc1"));
    addToSolver(q == getMemObjAddress("malloc2"));
    storeValue(p, q);
    storeValue(q, getZ3Expr(10));
    addToSolver(r == loadValue(p));
    addToSolver(x == loadValue(r));

    printExprValues();
    addToSolver(x == getZ3Expr(10));
    std::cout << solver.check() << std::endl;
}

/*
   // Array and pointers

    int main() {
        int* p;
        int* x;
        int* y;
        int a;
        int b;
        p = malloc;
        x = &p[0];
        y = &p[1]
        *x = 10;
        *y = 11;
        a = *x;
        b = *y;
        assert((a + b)>20);
    }
*/
void Z3Tests::test4()
{
    /// TODO: your code starts from here
    expr p = getZ3Expr("p");
    expr x = getZ3Expr("x");
    expr y = getZ3Expr("y");
    expr a = getZ3Expr("a");
    expr b = getZ3Expr("b");

    addToSolver(p == getMemObjAddress("malloc"));
    addToSolver(x == p);
    addToSolver(y == getGepObjAddress(p, 1));
    storeValue(x, getZ3Expr(10));
    storeValue(y, getZ3Expr(11));
    addToSolver(a == loadValue(x));
    addToSolver(b == loadValue(y));

    printExprValues();
    addToSolver(a + b > getZ3Expr(20));
    std::cout << solver.check() << std::endl;    
}

/*
    // Branches

int main(int argv) {
    int a;
    int b;
    int b1;
    a = argv + 1;
    b = 5;
    if(a > 10)
        b = a;
    b1 = b;
    assert(b1 >= 5);
}
*/
void Z3Tests::test5()
{
    /// TODO: your code starts from here
    expr argv = getZ3Expr("argv");
    expr a = getZ3Expr("a");
    expr b = getZ3Expr("b");
    expr b1 = getZ3Expr("b1");

    addToSolver(a == argv + getZ3Expr(1));
    addToSolver(b == ite(a > getZ3Expr(10), a, getZ3Expr(5)));
    addToSolver(b1 == b);

    printExprValues();
    addToSolver(b1 >= getZ3Expr(5));
    std::cout << solver.check() << std::endl;
}

/*
// Compare and pointers
int main() {
   int *a = malloc1;
   int *b = malloc2;
   *a = 5;
   *b = 10;
   int *p;
   if (*a < *b) {
       p = a;
   } else {
       p = b;
   }
   assert(*p == 5);
}
*/
void Z3Tests::test6()
{
    /// TODO: your code starts from here
    expr a = getZ3Expr("a");
    expr b = getZ3Expr("b");
    expr p = getZ3Expr("p");

    addToSolver(a == getMemObjAddress("malloc1"));
    addToSolver(b == getMemObjAddress("malloc2"));
    storeValue(a, getZ3Expr(5));
    storeValue(b, getZ3Expr(10));
    addToSolver(p == ite(loadValue(a) < loadValue(b), a, b));

    printExprValues();
    addToSolver(loadValue(p) == getZ3Expr(5));
    std::cout << solver.check() << std::endl;
}

/*
 int main() {
	int a = 1, b = 2, c = 3;
	int d;
  if (a > 0) {
  	d = b + c;
  }
  else {
  	d = b - c;
  }
  assert(d == 5);
 }
 */
void Z3Tests::test7()
{
    /// TODO: your code starts from here
    expr a = getZ3Expr("a");
    expr b = getZ3Expr("b");
    expr c = getZ3Expr("c");
    expr d = getZ3Expr("d");

    addToSolver(a == getZ3Expr(1));
    addToSolver(b == getZ3Expr(2));
    addToSolver(c == getZ3Expr(3));
    addToSolver(d == ite(a > getZ3Expr(0), b + c, b - c));

    printExprValues();
    addToSolver(d == getZ3Expr(5));
    std::cout << solver.check() << std::endl;
}

/*
 int main() {
    int arr[2] = {0, 1};
    int a = 10;
    int *p;
    if (a > 5) {
        p = &arr[0];
    }
    else {
        p = &arr[1];
    }
    assert(*p == 0);
 }
 */
void Z3Tests::test8()
{
    /// TODO: your code starts from here
    expr arr = getZ3Expr("arr");// 符号变量作为数组基指针
    addToSolver(arr == getMemObjAddress("arr"));// 约束到虚拟内存地址

    expr arr1 = getGepObjAddress(arr, 1);
    storeValue(arr,  getZ3Expr(0));
    storeValue(arr1, getZ3Expr(1));

    expr a = getZ3Expr("a");
    expr p = getZ3Expr("p");
    addToSolver(a == getZ3Expr(10));
    addToSolver(p == ite(a > getZ3Expr(5), arr, arr1));

    printExprValues();
    addToSolver(loadValue(p) == getZ3Expr(0));
    std::cout << solver.check() << std::endl;
}

/*
    // Struct and pointers

    struct A{ int f0; int* f1;};
    int main() {
       struct A* p;
       int* x;
       int* q;
       int** r;
       int* y;
       int z;

       p = malloc1;
       x = malloc2;
       *x = 5;
       q = &(p->f0);
       *q = 10;
       r = &(p->f1);
       *r = x;
       y = *r;
       z = *q + *y;
       assert(z == 15);
    }
*/
void Z3Tests::test9()
{
    /// TODO: your code starts from here
    expr p = getZ3Expr("p");
    expr x = getZ3Expr("x");
    expr q = getZ3Expr("q");
    expr r = getZ3Expr("r");
    expr y = getZ3Expr("y");
    expr z = getZ3Expr("z");

    addToSolver(p == getMemObjAddress("malloc1"));
    addToSolver(x == getMemObjAddress("malloc2"));
    storeValue(x, getZ3Expr(5));
    addToSolver(q == getGepObjAddress(p, 0));
    storeValue(q, getZ3Expr(10));
    addToSolver(r == getGepObjAddress(p, 1));
    storeValue(r, x);
    addToSolver(y == loadValue(r));
    addToSolver(z == loadValue(q) + loadValue(y));

    printExprValues();
    addToSolver(z == getZ3Expr(15));
    std::cout << solver.check() << std::endl;
}

/*
int foo(int z) {
    k = z;
    return k;
}
int main() {
  int x;
  int y;
  y = foo(2);
  x = foo(3);
  assert(x == 3 && y == 2);
}
*/
void Z3Tests::test10()
{
    /// TODO: your code starts from here
    expr k1 = getZ3Expr("k1");
    expr k2 = getZ3Expr("k2");
    expr x = getZ3Expr("x");
    expr y = getZ3Expr("y");

    addToSolver(k1 == getZ3Expr(2));
    addToSolver(y == k1);
    addToSolver(k2 == getZ3Expr(3));
    addToSolver(x == k2);

    printExprValues();
    addToSolver((x == getZ3Expr(3)) && (y == getZ3Expr(2)));
    std::cout << solver.check() << std::endl;
}


int main()
{
    Z3Tests tests;
    tests.test0();
    tests.solver.reset();
    tests.test1();
    tests.solver.reset();
    tests.test2();
    tests.solver.reset();
    tests.test3();
    tests.solver.reset();
    tests.test4();
    tests.solver.reset();
    tests.test5();
    tests.solver.reset();
    tests.test6();
    tests.solver.reset();
    tests.test7();
    tests.solver.reset();
    tests.test8();
    tests.solver.reset();
    tests.test9();
    tests.solver.reset();
    tests.test10();

    return 0;
}