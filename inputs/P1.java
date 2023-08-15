//with synchronized on same object
class T7 {
	public static void main(String[] args) {
		try {
			T7A a;
			T7A b;
			T7 c;
			a = new T7A();
			b = new T7A();
			a.f = b;
			a.start();
			synchronized(b) {
				c = new T7();
				a.f1 = c;
			}
			a.join();
			
			
		}catch(Exception e) {
			
		}
	}
}
class T7A extends Thread{
	T7A f;
	T7 f1;
	public void run() {
		try {
			T7 d;
			synchronized(f) {
				d = f1;
				System.out.println(d);
			}
		}catch(Exception e) {
			
		}
	}
}
class P1{}