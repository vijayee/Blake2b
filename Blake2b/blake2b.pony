use "collections"

interface Hasher
  fun ref update(data: Array[U8] box)
  fun ref digest() : Array[U8]

primitive _Sigma
  fun apply(): Array[Array[U8]] =>
    [
      [  0;  1;  2;  3;  4;  5;  6;  7;  8;  9; 10; 11; 12; 13; 14; 15 ]
      [ 14; 10;  4;  8;  9; 15; 13;  6;  1; 12;  0;  2; 11;  7;  5;  3 ]
      [ 11;  8; 12;  0;  5;  2; 15; 13; 10; 14;  3;  6;  7;  1;  9;  4 ]
      [  7;  9;  3;  1; 13; 12; 11; 14;  2;  6;  5; 10;  4;  0; 15;  8 ]
      [  9;  0;  5;  7;  2;  4; 10; 15; 14;  1; 11; 12;  6;  8;  3; 13 ]
      [  2; 12;  6; 10;  0; 11;  8;  3;  4; 13;  7;  5; 15; 14;  1;  9 ]
      [ 12;  5;  1; 15; 14; 13;  4; 10;  0;  7;  6;  3;  9;  2;  8; 11 ]
      [ 13; 11;  7; 14; 12;  1;  3;  9;  5;  0; 15;  4;  8;  6;  2; 10 ]
      [  6; 15; 14;  9; 11;  3;  0;  8; 12;  2; 13;  7;  1;  4; 10;  5 ]
      [ 10;  2;  8;  4;  7;  6;  1;  5; 15; 11;  9; 14;  3; 12; 13 ; 0 ]
      [  0;  1;  2;  3;  4;  5;  6;  7;  8;  9; 10; 11; 12; 13; 14; 15 ]
      [ 14; 10;  4;  8;  9; 15; 13;  6;  1; 12;  0;  2; 11;  7;  5;  3 ]
    ]
primitive _IV
  fun apply(): Array[U64] =>
    [
      0x6a09e667f3bcc908; 0xbb67ae8584caa73b
      0x3c6ef372fe94f82b; 0xa54ff53a5f1d36f1
      0x510e527fade682d1; 0x9b05688c2b3e6c1f
      0x1f83d9abfb41bd6b; 0x5be0cd19137e2179
    ]
class Blake2b
  var _digestSize: USize
  var _h: Array[U64] // hash
  var _t: Array[U64] // counter
  var _f: Array[U64] // finalization flags
  var _buf: Array[U8] // ring buffer
  let _blockBytes: USize = 128
  let _iv: Array[U64]
  let _sigma: Array[Array[U8]]

  new create(digestSize: USize = 32) =>
    _digestSize = if digestSize > _blockBytes then _blockBytes else digestSize end
    _t = Array[U64].init(0, 2)
    _f = Array[U64].init(0, 2)
    _h = _IV()
    _iv = _IV()
    _sigma = _Sigma()
    _buf = Array[U8](_blockBytes)

  new key(digestSize: USize = 32, key': Array[U8])? =>
    _digestSize = if digestSize > _blockBytes then _blockBytes else digestSize end
    _t = Array[U64].init(0, 2)
    _f = Array[U64].init(0, 2)
    _h = _IV()
    _iv = _IV()
    _sigma = _Sigma()
    _buf = Array[U8](_blockBytes)
    var k: U64 = 0
    var j: USize = 0
    var i: USize = 0
    // XOR key with IV
    while  i < key'.size() do
      k = k + ((key'(i)?.u64() and 0xff) << (i.u64() * 8))
      if (i % 8) == 7 then
        _h(i)? = _h(i)? xor k
        k = 0
        j = j + 1
        if j >= _h.size() then
          break
        end
      end
      i = i + 1
    end
  fun ref digest(): Array[U8] iso^ =>
    var buffer: Array[U8] = Array[U8](_digestSize)
    if not _isLastBlock() then // digest has already been issued
      _incrementCounter(_buf.size().u64())
      _setLastBlock()
      //pad buffer with 0 if it has less than the block size elements
      for c in Range(0, _blockBytes - _buf.size()) do
        _buf.push(0)
      end
      //compress current buffer into hash
      _compress(_buf)
    end
    //convert hash to little endian and return it
    var shift: USize = 0
    for h in _h.values() do
      shift = 0
      for i in Range(0, 8) do
        shift = 8 * i
        buffer.push(((h >> shift.u64()) and 0xFF).u8())
        if buffer.size() == _digestSize then
          let buffer': Array[U8] iso = recover Array[U8](_digestSize) end
          for c in buffer.values() do
            buffer'.push(c)
          end
          return consume buffer'
        end
      end
    end
    buffer = buffer.slice(0, _digestSize)
    let buffer': Array[U8] iso = recover Array[U8](_digestSize) end
    for c in buffer.values() do
      buffer'.push(c)
    end
    consume buffer'

  fun ref update(data: Array[U8] box) =>
    var dataSize: USize = data.size()
    if dataSize > 0 then
      var left: USize = _buf.size()
      // Find the difference between the buffer size and the block size in bytes
      var fill: USize = _blockBytes - left
      var i : USize = 0
      //If data is greater than the size left in the buffer
      if dataSize > fill then
        // fill the remaining buffer space with the first bytes of data
        _buf.append(data.slice(0, fill))
        // Compress by one block size
        _incrementCounter(_blockBytes.u64())
        _compress(_buf)
        //ignore data already in buffer by pushing the index beyond it
        i = i + fill
        // keep track of the size of data we've already processed
        dataSize = dataSize - fill
        // Compress until there is only one block left
        // process one block size at a time
        while dataSize > _blockBytes.usize() do
          _incrementCounter(_blockBytes.u64())
          _compress(data.slice(i, (i + _blockBytes)))
          i = i + _blockBytes
          dataSize = dataSize - _blockBytes
        end
        // Rollover the buffer with input data till it meets the the original
        // block size difference for the buffer
        for j in Range(0, dataSize) do
          for k  in Range(i, i + dataSize) do
            try _buf(j)? = data(k)? end
          end
        end
      else
        _buf.append(data)
      end
    end

  fun ref _incrementCounter(inc: U64) =>
    try
      _t(0)? = _t(0)? + inc
      _t(1)? = _t(1)? + (if (_t(0)? < inc) then 1 else 0 end)
    end
  fun ref _compress(block: Array[U8]) =>
    var m: Array[U64] = Array[U64].init(0, 16)
    var v: Array[U64] = Array[U64].init(0, 16)
    var index: USize = 0
    var m': U64 = 0
    for i in Range(0, 16) do
      try
        m' = 0
        for j in Range(index, index + 8) do
          m' =  m' + ((block(j)?.u64() and 0xff) << (j.u64() * 8))
        end
        m(i)? = m'
        index = index + 64
      end
    end
    for i in Range(0, 8) do
      try v(i)? = _h(i)? end
    end
    for i in Range(0, 4) do
      try v(i + 8)? = _iv(i)? end
    end
    try
      v(12)? = _iv(4)? xor _t(0)?
      v(13)? = _iv(5)? xor _t(1)?
      v(14)? = _iv(6)? xor _t(0)?
      v(15)? = _iv(7)? xor _t(1)?
    end
    for i in Range(0, 12) do
      try _round(i, m, v)? end
    end
    for i in Range(0, 8) do
      try _h(i)? = (_h(i)? xor v(i)?) xor v(i + 8)? end
    end

  fun ref _round(r: USize, m: Array[U64], v: Array[U64]) ?  =>
      _g(r, 0, 0, 4, 8, 12, m, v)?
      _g(r, 1, 1, 5, 9, 13, m, v)?
      _g(r, 2, 2, 6, 10, 14, m, v)?
      _g(r, 3, 3, 7, 11, 15, m, v)?
      _g(r, 4, 0, 5, 10, 15, m, v)?
      _g(r, 5, 1, 6, 11, 12, m, v)?
      _g(r, 6, 2, 7, 8, 13, m, v)?
      _g(r, 7, 3, 4, 9, 14, m, v)?

  fun ref _g(r: USize,i: USize, a:USize, b: USize, c: USize, d:USize, m: Array[U64], v: Array[U64]) ? =>
    v(a)? = v(a)? + v(b)? + m(_sigma(r)?((2 * i) + 0)?.usize())?
    v(d)? = (v(d)? xor v(a)?).rotr(32)
    v(c)? = v(c)? + v(d)?
    v(b)? = (v(b)? xor v(c)?).rotr(24)
    v(a)? = v(a)? + v(b)? + m(_sigma(r)?((2 * i) + 1)?.usize())?
    v(d)? = (v(d)? xor v(a)?).rotr(16)
    v(c)? = v(c)? + v(d)?
    v(b)? = (v(b)? xor v(c)?).rotr(63)

  fun _isLastBlock(): Bool =>
    try _f(0)? != 0 else false end

  fun ref _setLastNode() =>
    try _f(1)? =  U64(-1) end

  fun ref _setLastBlock() =>
    try  _f(0)? = U64(-1) end
