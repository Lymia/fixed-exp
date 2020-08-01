use criterion::{black_box, criterion_group, criterion_main, Criterion};
use fixed::types::{I16F16, I32F32};

use fixed_exp::*;

fn bench_powi(c: &mut Criterion) {
    let base_fixed_32 = I16F16::from_num(1.4);
    let base_fixed_64 = I32F32::from_num(1.4);

    c.bench_function("f64 powi (small exponent)", |b| {
        b.iter(|| black_box(1.4f64).powi(black_box(7)))
    });
    c.bench_function("f32 powi (small exponent)", |b| {
        b.iter(|| black_box(1.4f32).powi(black_box(7)))
    });
    c.bench_function("I16F16 powi (small exponent)", |b| {
        b.iter(|| black_box(base_fixed_32).powi(black_box(7)))
    });
    c.bench_function("I32F32 powi (small exponent)", |b| {
        b.iter(|| black_box(base_fixed_64).powi(black_box(7)))
    });

    c.bench_function("f64 powi (large exponent)", |b| {
        b.iter(|| black_box(1.4f64).powi(black_box(42)))
    });
    c.bench_function("f32 powi (large exponent)", |b| {
        b.iter(|| black_box(1.4f32).powi(black_box(42)))
    });
    c.bench_function("I16F16 powi (large exponent)", |b| {
        b.iter(|| black_box(base_fixed_32).powi(black_box(42)))
    });
    c.bench_function("I32F32 powi (large exponent)", |b| {
        b.iter(|| black_box(base_fixed_64).powi(black_box(42)))
    });
}

fn bench_powf(c: &mut Criterion) {
    let base_fixed_32 = I16F16::from_num(1.4);
    let base_fixed_64 = I32F32::from_num(1.4);

    let small_exp_fixed_32 = I16F16::from_num(9.6);
    let small_exp_fixed_64 = I32F32::from_num(9.6);

    let large_exp_fixed_32 = I16F16::from_num(42.54);
    let large_exp_fixed_64 = I32F32::from_num(42.54);

    c.bench_function("f64 powf (small exponent)", |b| {
        b.iter(|| black_box(1.4f64).powf(black_box(9.6)))
    });
    c.bench_function("f32 powf (small exponent)", |b| {
        b.iter(|| black_box(1.4f32).powf(black_box(9.6)))
    });
    c.bench_function("I16F16 powf (small exponent)", |b| {
        b.iter(|| black_box(base_fixed_32).powf(black_box(small_exp_fixed_32)))
    });
    c.bench_function("I32F32 powf (small exponent)", |b| {
        b.iter(|| black_box(base_fixed_64).powf(black_box(small_exp_fixed_64)))
    });

    c.bench_function("f64 powf (large exponent)", |b| {
        b.iter(|| black_box(1.4f64).powf(black_box(42.54)))
    });
    c.bench_function("f32 powf (large exponent)", |b| {
        b.iter(|| black_box(1.4f32).powf(black_box(42.54)))
    });
    c.bench_function("I16F16 powf (large exponent)", |b| {
        b.iter(|| black_box(base_fixed_32).powf(black_box(large_exp_fixed_32)))
    });
    c.bench_function("I32F32 powf (large exponent)", |b| {
        b.iter(|| black_box(base_fixed_64).powf(black_box(large_exp_fixed_64)))
    });
}

criterion_group!(benches, bench_powi, bench_powf);
criterion_main!(benches);
