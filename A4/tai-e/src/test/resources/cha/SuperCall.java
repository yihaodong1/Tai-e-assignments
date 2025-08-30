public class SuperCall {

    public static void main(String[] args) {
        A a = new B();
        a.foo();
    }
}

class A {
    void foo() {
    }
}

class B extends A {
    void foo() {
        super.foo();
    }
}