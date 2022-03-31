
use std::cmp;

//#define ROTL(x,y) (((x)<<(y&(w-1))) | ((x)>>(w-(y&(w-1)))))
fn rotl(a: u32, w: u32, offset: u32) -> u32 {
    let r1 = a << offset;
    let r2 = a >> (w - offset);
    r1 | r2
}

//#define ROTR(x,y) (((x)>>(y&(w-1))) | ((x)<<(w-(y&(w-1)))))
fn rotr(a: u32, w: u32, offset: u32) -> u32 {
    let r1 = a >> offset;
    let r2 = a << (w - offset);
    r1 | r2
}

fn aligne_key(key: Vec<u8>, w: u32) -> Vec<u32> {
    let b = (key.len() - 1) as u32;
    let u = w >> 3;
    let mut i: i32 = (key.len() - 1) as i32;
    let c = if b % u > 0 { b / u + 1 } else { b / u }; // c = b % u > 0 ? b / u + 1 : b / u;

    let mut l = vec![0; c as usize];
    //for (i = b - 1; i >= 0; i--)
    while i >= 0 {
        l[i as usize / u as usize] =
            rotl(l[i as usize / u as usize], w, 8) + (key[i as usize]) as u32; //  L [i / u] = ROL(L[i / u], 8) + key[i];
        i = i - 1;
    }
    l
}

// Initializing sub-key S.
fn sub_keys(p: u32, q: u32, r: u32) -> Vec<u32> {
    let t = 2 * (r + 1);
    let mut s = vec![0; t as usize];
    s[0] = p;
    for i in 1..t {
        //for (i = 1; i < t; i++)
        s[i as usize] = s[(i as usize - 1)] + q;
    }
    s
}

// Sub-key mixing.
fn sub_keys_mix(key: Vec<u8>, mut l: Vec<u32>, mut s: Vec<u32>, r: u32, w: u32) -> Vec<u32> {
    let mut x = 0;
    let mut y = 0;
    let mut j = 0;
    let mut i = 0;
    let b = (key.len() - 1) as u32;
    let u = w >> 3;
    let c = if b % u > 0 { b / u + 1 } else { b / u };
    let t = 2 * (r + 1);
    let n = 3 * cmp::max(t, c); // n = 3 * Math.Max(t, c);

    for _k in 0..n {
        // for (int k = 0; k < n; k++)
        s[i as usize] = rotl(s[i as usize] + x + y, w, 3);
        x = s[i as usize];
        l[j as usize] = rotl(l[j] + x + y, w, (x + y) as u32);
        y = l[j as usize];
        i = (i + 1) % t;
        j = (j + 1) % c as usize;
    }
    s
}

fn bytes2u32(d: Vec<u8>) -> u32 {
    d[0] as u32 + d[1] as u32 * 256 + d[2] as u32 * 256 * 256 + d[3] as u32 * 256 * 256 * 256
}

fn u32vec(d: u32) -> Vec<u8> {
    let v = vec![
        (d & 0xff) as u8,
        ((d & 0xff00) / 256) as u8,
        ((d & 0xff0000) >> 16) as u8,
        ((d & 0xff000000) >> 24) as u8,
    ];
    v
}

pub fn encode(key: Vec<u8>, plaintext: Vec<u8>, r: u32, w: u32, p: u32, q: u32) -> Vec<u8> {
    let c = plaintext.len() / 2;
    let pt = plaintext.clone();
    let av: Vec<_> = pt[0..c].iter().cloned().collect();
    let bv: Vec<_> = pt[c..pt.len()].iter().cloned().collect();
    let mut a = bytes2u32(av.clone());
    let mut b = bytes2u32(bv.clone());

    let ak = aligne_key(key.clone(), w);
    let sk = sub_keys(p, q, r);
    let s = sub_keys_mix(key, ak, sk, r, w);

    a = a + s[0];
    b = b + s[1];

    for i in 1..r + 1 {
        // for (int i = 1; i < R + 1; i++) {
        a = rotl(a ^ b, w, b) + s[2 * i as usize];
        b = rotl(b ^ a, w, a) + s[2 * i as usize + 1];
    }

    let mut ciphertext = u32vec(a);
    let cb = u32vec(b);
    ciphertext.extend(cb);
    ciphertext
}

/*
 * This function should return a plaintext for a given key and ciphertext
 *
 */
pub fn decode(key: Vec<u8>, plaintext: Vec<u8>, r: u32, w: u32, p: u32, q: u32) -> Vec<u8> {
    let c = plaintext.len() / 2;
    let pt = plaintext.clone();
    let av: Vec<_> = pt[0..c].iter().cloned().collect();
    let bv: Vec<_> = pt[c..pt.len()].iter().cloned().collect();
    let mut a = bytes2u32(av.clone());
    let mut b = bytes2u32(bv.clone());

    let ak = aligne_key(key.clone(), w);
    let sk = sub_keys(p, q, r);
    let s = sub_keys_mix(key, ak, sk, r, w);

    let mut i = r;
    while i > 0 {
        //for (int i = R; i > 0; i--) {
        b = rotr(b - s[2 * i as usize + 1], w, a) ^ a;
        a = rotr(a - s[2 * i as usize], w, b) ^ b;
        i = i - 1;
    }

    b = b - s[1];
    a = a - s[0];

    let mut ciphertext = u32vec(a);
    let cb = u32vec(b);
    ciphertext.extend(cb);
    ciphertext
}

#[cfg(test)]
mod tests {
use super::*;

const W32: u32 = 32; // machine word as half of block
const R12: u32 = 12; // rounds, if zero no encoding
const P32: u32 = 0xb7e15163; // magic nunber P for w =32 as Pw = Odd((f - 1) * 2^W;
const Q32: u32 = 0x9e3779b9; // magic number Q for Q =32 as Qw = Odd((e - 2) * 2^W;

    #[test]
    fn encode_a() {
        let key = vec![
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D,
            0x0E, 0x0F,
        ];
        let pt = vec![0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77];
        let ct = vec![0x2D, 0xDC, 0x14, 0x9B, 0xCF, 0x08, 0x8B, 0x9E];
        let res = encode(key.clone(), pt, R12, W32, P32, Q32);
        assert!(&ct[..] == &res[..]);
    }

    #[test]
    fn encode_b() {
        let key = vec![
            0x2B, 0xD6, 0x45, 0x9F, 0x82, 0xC5, 0xB3, 0x00, 0x95, 0x2C, 0x49, 0x10, 0x48, 0x81,
            0xFF, 0x48,
        ];
        let pt = vec![0xEA, 0x02, 0x47, 0x14, 0xAD, 0x5C, 0x4D, 0x84];
        let ct = vec![0x11, 0xE4, 0x3B, 0x86, 0xD2, 0x31, 0xEA, 0x64];
        let res = encode(key.clone(), pt, R12, W32, P32, Q32);
        assert!(&ct[..] == &res[..]);
    }

    #[test]
    fn decode_a() {
        let key = vec![
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D,
            0x0E, 0x0F,
        ];
        let pt = vec![0x96, 0x95, 0x0D, 0xDA, 0x65, 0x4A, 0x3D, 0x62];
        let ct = vec![0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77];
        let res = decode(key, ct, R12, W32, P32, Q32);
        assert!(&pt[..] == &res[..]);
    }

    #[test]
    fn decode_b() {
        let key = vec![
            0x2B, 0xD6, 0x45, 0x9F, 0x82, 0xC5, 0xB3, 0x00, 0x95, 0x2C, 0x49, 0x10, 0x48, 0x81,
            0xFF, 0x48,
        ];
        let pt = vec![0x63, 0x8B, 0x3A, 0x5E, 0xF7, 0x2B, 0x66, 0x3F];
        let ct = vec![0xEA, 0x02, 0x47, 0x14, 0xAD, 0x5C, 0x4D, 0x84];
        let res = decode(key, ct, R12, W32, P32, Q32);
        assert!(&pt[..] == &res[..]);
    }
}
