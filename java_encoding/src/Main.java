import java.io.FileInputStream;
import java.io.IOException;
import java.nio.ByteBuffer;
import java.nio.CharBuffer;
import java.nio.channels.FileChannel;
import java.nio.charset.Charset;
import java.nio.charset.CharsetDecoder;
import java.nio.charset.CodingErrorAction;

public class Main {
    public static void main(String[] args) {
        // 文字化けが発生している行を抜き出したCSV
        String filePath = "/path/to/debug.csv";

        try (FileInputStream fis = new FileInputStream(filePath);
             FileChannel fileChannel = fis.getChannel()) {

            // EUC-JPのCharsetとCharsetDecoderを取得
            Charset charset = Charset.forName("x-eucJP-Open");
            CharsetDecoder decoder = charset.newDecoder();
            decoder.onMalformedInput(CodingErrorAction.REPORT);  // 不正なバイト列の処理方法を設定
            decoder.onUnmappableCharacter(CodingErrorAction.REPORT); // マッピングできない文字の処理方法を設定

            // ファイル全体をバッファに読み込む
            ByteBuffer byteBuffer = ByteBuffer.allocate((int) fileChannel.size());
            fileChannel.read(byteBuffer);
            byteBuffer.flip();

            // バイトバッファをCharBufferにデコード
            CharBuffer charBuffer = decoder.decode(byteBuffer);

            // デコードした内容を出力
            System.out.println(charBuffer.toString());

        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}