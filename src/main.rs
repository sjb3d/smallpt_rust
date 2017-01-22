use std::ops::{Add, Sub, Mul, Neg};
use std::fs::File;
use std::io::{Write, Result};
use std::{thread, time};
use std::sync::atomic::{AtomicUsize, Ordering, ATOMIC_USIZE_INIT};
use std::sync::{Arc, Mutex};
use std::env;

type F = f64;
use std::f64::consts::PI;

#[derive(Debug, Copy, Clone)]
struct Vec3 {
	x: F,
	y: F,
	z: F,
}

impl Add for Vec3 {
	type Output = Vec3;
	fn add(self, other: Vec3) -> Vec3 {
		Vec3{ x: self.x + other.x, y: self.y + other.y, z: self.z + other.z }
	}
}

impl Sub for Vec3 {
	type Output = Vec3;
	fn sub(self, other: Vec3) -> Vec3 {
		Vec3{ x: self.x - other.x, y: self.y - other.y, z: self.z - other.z }
	}
}

impl Mul for Vec3 {
	type Output = Vec3;
	fn mul(self, other: Vec3) -> Vec3 {
		Vec3{ x: self.x*other.x, y: self.y*other.y, z: self.z*other.z }
	}
}

impl Mul<F> for Vec3 {
	type Output = Vec3;
	fn mul(self, other: F) -> Vec3 {
		Vec3{ x: self.x*other, y: self.y*other, z: self.z*other }
	}
}

impl Neg for Vec3 {
	type Output = Vec3;
	fn neg(self) -> Vec3 {
		Vec3{ x: -self.x, y: -self.y, z: -self.z }
	}
}

fn dot(a: Vec3, b: Vec3) -> F {
	a.x*b.x + a.y*b.y + a.z*b.z
}

fn cross(a: Vec3, b: Vec3) -> Vec3 {
	Vec3{
		x: a.y*b.z - a.z*b.y,
		y: a.z*b.x - a.x*b.z,
		z: a.x*b.y - a.y*b.x
	}
}

impl Vec3 {
	fn norm(self) -> Vec3 {
		self*(1.0/dot(self, self).sqrt())
	}
}

#[derive(Debug, Copy, Clone)]
struct Ray {
	o: Vec3,
	d: Vec3,
}

#[derive(Debug, Copy, Clone)]
enum Refl {
	Diff,
	Spec,
	Refr,
}

#[derive(Debug)]
struct Sphere {
	rad: F,
	p: Vec3,
	e: Vec3,
	c: Vec3,
	refl: Refl,
}

impl Sphere {
	fn intersect(&self, r: Ray) -> Option<F> {
		// Solve t^2*d.d + 2*t*(o-p).d + (o-p).(o-p)-R^2 = 0
		let op = self.p - r.o;
		const EPS: F = 1.0e-4;
		let b = dot(op, r.d);
		let mut det = b*b - dot(op, op) + self.rad*self.rad;
		if det < 0.0 {
			None
		} else {
			det = det.sqrt();
			let t1 = b - det;
			let t2 = b + det;
			if t1 > EPS { Some(t1) } else if t2 > EPS { Some(t2) } else { None }
		}
	}
}

static SPHERES: [Sphere; 9] = [
	Sphere {
		rad: 1.0e5,
		p: Vec3{ x: 1.0e5 + 1.0, y: 40.8, z: 81.6 },
		e: Vec3{ x: 0.0, y: 0.0, z: 0.0 },
		c: Vec3{ x: 0.75, y: 0.25, z: 0.25 },
		refl: Refl::Diff
	},//Left
	Sphere {
		rad: 1.0e5,
		p: Vec3{ x: -1.0e5 + 99.0, y: 40.8, z: 81.6 },
		e: Vec3{ x: 0.0, y: 0.0, z: 0.0 },
		c: Vec3{ x: 0.25, y: 0.25, z: 0.75 },
		refl: Refl::Diff
	},//Rght
	Sphere {
		rad: 1.0e5,
		p: Vec3{ x: 50.0, y: 40.8, z: 1.0e5 },
		e: Vec3{ x: 0.0, y: 0.0, z: 0.0 },
		c: Vec3{ x: 0.75, y: 0.75, z: 0.75 },
		refl: Refl::Diff
	},//Back
	Sphere {
		rad: 1.0e5,
		p: Vec3{ x: 50.0, y: 40.8, z: -1.0e5 + 170.0 },
		e: Vec3{ x: 0.0, y: 0.0, z: 0.0 },
		c: Vec3{ x: 0.0, y: 0.0, z : 0.0 },
		refl: Refl::Diff
	},//Frnt
	Sphere {
		rad: 1.0e5,
		p: Vec3{ x: 50.0, y: 1.0e5, z: 81.6 },
		e: Vec3{ x: 0.0, y: 0.0, z: 0.0 },
		c: Vec3{ x: 0.75, y: 0.75, z: 0.75 },
		refl: Refl::Diff
	},//Botm
	Sphere {
		rad: 1.0e5,
		p: Vec3{ x: 50.0, y: -1.0e5 + 81.6, z: 81.6 },
		e: Vec3{ x: 0.0, y: 0.0, z: 0.0 },
		c: Vec3{ x: 0.75, y: 0.75, z: 0.75 },
		refl: Refl::Diff
	},//Top
	Sphere {
		rad: 16.5,
		p: Vec3{ x: 27.0, y: 16.5, z: 47.0 },
		e: Vec3{ x: 0.0, y: 0.0, z: 0.0 },
		c: Vec3{ x: 0.999, y: 0.999, z: 0.999 },
		refl: Refl::Spec
	},//Mirr
	Sphere {
		rad: 16.5,
		p: Vec3{ x: 73.0, y: 16.5, z: 78.0 },
		e: Vec3{ x: 0.0, y: 0.0, z: 0.0 },
		c: Vec3{ x: 0.999, y: 0.999, z: 0.999 },
		refl: Refl::Refr
	},//Glas
	Sphere {
		rad: 600.0,
		p: Vec3{ x: 50.0, y: 681.6 - 0.27, z: 81.6 },
		e: Vec3{ x: 12.0, y: 12.0, z: 12.0 },
		c: Vec3{ x: 0.0, y: 0.0, z: 0.0 },
		refl: Refl::Diff
	},//Lite
];

fn clamp(x: F) -> F {
	x.min(1.0).max(0.0)
}

fn to_int(x: F) -> i32 {
	(clamp(x).powf(1.0/2.2)*255.0 + 0.5) as i32
}

#[derive(Debug, Copy, Clone)]
struct Hit {
	t: F,
	id: usize,
}

fn intersect(r: Ray) -> Option<Hit> {
	let mut hit: Option<Hit> = None;
	for (i, s) in SPHERES.into_iter().enumerate() {
		if let Some(d) = s.intersect(r) {
			let is_closer = if let Some(h) = hit { d < h.t } else { true };
			if is_closer {
				hit = Some(Hit{ t: d, id: i });
			}
		}
	}
	hit
}

struct RandomState {
	s: u64,
}

fn erand48(xi: &mut RandomState) -> F {
	xi.s = xi.s.wrapping_mul(0x5deece66du64).wrapping_add(0xbu64) & 0xffffffffffffu64;
	// would like to use ldexp here, but deprecated!
	((xi.s & 0xffffu64) as F)*2.0f64.powi(-16)
	+ (((xi.s >> 16) & 0xffffu64) as F)*2.0f64.powi(-32)
	+ (((xi.s >> 32) & 0xffffu64) as F)*2.0f64.powi(-48)
}

fn radiance(r: Ray, depth: i32, xi: &mut RandomState) -> Vec3 {
	if let Some(hit) = intersect(r) {
		let obj = &SPHERES[hit.id];

		let x = r.o + r.d*hit.t;
		let n = (x - obj.p).norm();
		let nl = if dot(n, r.d) < 0.0 { n } else { -n };
		let mut f = obj.c;

		let p = f.x.max(f.y).max(f.z); // max refl

		let depth = depth + 1;
		if depth > 5 {
			if erand48(xi) < p {
				f = f*(1.0/p);
			} else {
				return obj.e;
			}
		}

		match obj.refl {
			Refl::Diff => {
				let r1 = 2.0*PI*erand48(xi);
				let r2 = erand48(xi);
				let r2s = r2.sqrt();

				let w = nl;
				let u = cross(if w.x.abs() > 0.1 { Vec3{ x: 0.0, y: 1.0, z: 0.0 } } else { Vec3{ x: 1.0, y: 0.0, z: 0.0 } }, w).norm();
				let v = cross(w, u);

				let d = (u*r1.cos()*r2s + v*r1.sin()*r2s + w*(1.0 - r2).sqrt()).norm();

				obj.e + f*radiance(Ray{ o: x, d: d }, depth, xi)
			},
			Refl::Spec => {
				obj.e + f*radiance(Ray{ o: x, d: r.d - n*2.0*dot(n, r.d) }, depth, xi)
			},
			Refl::Refr => {
				let refl_ray = Ray{ o: x, d: r.d - n*2.0*dot(n, r.d) };

				let into = dot(n, nl) > 0.0;

				let nc = 1.0;
				let nt = 1.5;
				let nnt = if into { nc/nt } else { nt/nc };
				let ddn = dot(r.d, nl);

				let cos2t = 1.0 - nnt*nnt*(1.0 - ddn*ddn);
				if cos2t < 0.0 {
					obj.e + f*radiance(refl_ray, depth, xi)
				} else {
					let tdir = (r.d*nnt - n*(if into { 1.0 } else { -1.0 })*(ddn*nnt + cos2t.sqrt())).norm();

					let a = nt - nc;
					let b = nt + nc;
					let r_0 = a*a/(b*b);
					let c = 1.0 - if into { -ddn } else { dot(tdir, n) };

					let r_e = r_0 + (1.0 - r_0)*c*c*c*c*c;
					let t_r = 1.0 - r_e;
					let p = 0.25 + 0.5*r_e;
					let r_p = r_e/p;
					let t_p = t_r/(1.0 - p);

					obj.e + f*if depth > 2 {
						if erand48(xi) < p { radiance(refl_ray, depth, xi)*r_p } else { radiance(Ray{ o: x, d: tdir }, depth, xi)*t_p }
					} else {
						radiance(refl_ray, depth, xi)*r_e + radiance(Ray{ o: x, d: tdir }, depth, xi)*t_r
					}
				}
			},
		}
	} else {
		Vec3{ x: 0.0, y: 0.0, z: 0.0 }
	}
}

const W: usize = 1024;
const H: usize = 768;

type Row = Vec<Vec3>;
type Image = Vec<Row>;

fn write_output(image: &Image) -> Result<()> {
	let mut f = File::create("image.ppm")?;
	f.write_fmt(format_args!("P3\n{} {}\n{}\n", W, H, 255))?;
	for c in image {
		for r in c {
			f.write_fmt(format_args!("{} {} {} ", to_int(r.x), to_int(r.y), to_int(r.z)))?;
		}
	}
	Ok(())
}

static Y: AtomicUsize = ATOMIC_USIZE_INIT;
static DONE: AtomicUsize = ATOMIC_USIZE_INIT;

fn main() {
	let samps = if let Some(arg) = env::args().nth(1) { arg.parse::<usize>().unwrap()/4 } else { 1 };

	let cam = Ray{
		o: Vec3{ x: 50.0, y: 52.0, z: 295.6 },
		d: Vec3{ x: 0.0, y: -0.042612, z: -1.0 }.norm() };

	let cx = Vec3{ x: (W as F)*0.5135/(H as F), y: 0.0, z: 0.0 };
	let cy = cross(cx, cam.d).norm()*0.5135;

	let image_store = Arc::new(Mutex::new(vec![Row::new(); H]));

	const THREAD_COUNT: usize = 4;
	for _ in 0..THREAD_COUNT {
		let image_store = image_store.clone();
		let y = &Y;
		// recursive radiance function needs massive stack
		thread::Builder::new().stack_size(4*1024*1024).spawn(move || {
			loop {
				let y = y.fetch_add(1, Ordering::SeqCst);
				if y >= H as usize {
					break;
				}
				let mut xi = RandomState{ s: (y*y*y) as u64 };
				let mut c = Vec::with_capacity(W);
				for x in 0..W {
					let mut ci = Vec3{ x: 0.0, y: 0.0, z : 0.0 };
					for sy in 0..2 {
						for sx in 0..2 {
							let mut r = Vec3{ x: 0.0, y: 0.0, z : 0.0 };
							for _ in 0..samps {
								let r1 = 2.0*erand48(&mut xi);
								let r2 = 2.0*erand48(&mut xi);
								let dx = if r1 < 1.0 { r1.sqrt() - 1.0 } else { 1.0 - (2.0 - r1).sqrt() };
								let dy = if r2 < 1.0 { r2.sqrt() - 1.0 } else { 1.0 - (2.0 - r2).sqrt() };
								let d = cam.d
									+ cx*(((((sx as F) + 0.5 + dx)/2.0) + (x as F))/(W as F) - 0.5)
									+ cy*(0.5 - ((((sy as F) + 0.5 + dy)/2.0) + (y as F))/(H as F));
								r = r + radiance(Ray{ o: cam.o + d*140.0, d: d.norm() }, 0, &mut xi)*(1.0/(samps as F));
							}
							ci = ci + Vec3{ x: clamp(r.x), y: clamp(r.y), z: clamp(r.z) }*0.25;
						}
					}
					c.push(ci);
				}
				let mut image = image_store.lock().unwrap();
				image[y] = c;
			}
			DONE.fetch_add(1, Ordering::SeqCst);
		}).unwrap();
	}

	loop {
		let done = DONE.load(Ordering::SeqCst);
		if done == THREAD_COUNT {
			break;
		}
		let y = Y.load(Ordering::SeqCst);
		println!("rendering ({} spp) {:.1}%...", samps*4, 100.0*(y as F)/((H - 1) as F));
		thread::sleep(time::Duration::from_millis(200));
	}

	println!("writing output...");
	let _ = write_output(&image_store.lock().unwrap());
}
