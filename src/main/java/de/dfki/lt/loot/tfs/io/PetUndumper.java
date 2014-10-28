package de.dfki.lt.loot.tfs.io;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.nio.ByteBuffer;
import java.nio.ByteOrder;
import java.nio.channels.FileChannel;

public class PetUndumper {

  private FileChannel _channel;

  private ByteBuffer buf;

  public int undumpInt() { return buf.getInt(); }

  public short undumpShort() { return buf.getShort(); }

  public String undumpString() {
    int len = undumpShort();
    byte[] chars = new byte[len-1];
    buf.get(chars);
    byte zero = buf.get();
    assert(zero == 0);
    return new String(chars);
  }

  public int[] undumpBitcode(int codesize) throws IOException {
    int[] result = new int[codesize];
    int i = 0;
    while (i < codesize) {
      result[i] = undumpInt();
      if (result[i] == 0) {
        int l = undumpShort();
        while (--l > 0) {
          ++i;
          if (i >= codesize)
            throw new IOException("invalid compressed bitcode (too long)");
          result[i] = 0;
        }
      }
      ++i;
    }
    if( undumpInt() != 0 || undumpShort() != 0)
      throw new IOException("invalid compressed bitcode (no end marker)");
    return result;
  }

  public void seekAbsolute(int offset) throws IOException {
    buf.position(offset);
  }

  public void open(File aFile) throws FileNotFoundException, IOException {
    _channel = new RandomAccessFile(aFile, "r").getChannel();
    buf = _channel.map(FileChannel.MapMode.READ_ONLY, 0, (int) _channel.size());
    buf.order(ByteOrder.LITTLE_ENDIAN);
  }

  public void close() throws IOException {
    _channel.close();
  }
}
