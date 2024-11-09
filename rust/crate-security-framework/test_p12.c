// export OPENSSL_PATH=/opt/homebrew/opt/openssl@3
// gcc -o test_p12 test_p12.c -I"$OPENSSL_PATH/include" -L"$OPENSSL_PATH/lib" -lssl -lcrypto
#include <stdio.h>
#include <openssl/pkcs12.h>
#include <openssl/err.h>
#include <openssl/ssl.h>

int main() {
    const char *filename = "server.p12";
    const char *password = "bark";
    FILE *fp = fopen(filename, "rb");
    if (!fp) {
        perror("Cannot open file");
        return 1;
    }

    PKCS12 *p12 = d2i_PKCS12_fp(fp, NULL);
    fclose(fp);
    if (!p12) {
        fprintf(stderr, "Failed to read PKCS12 file\n");
        ERR_print_errors_fp(stderr);
        return 1;
    }

    EVP_PKEY *pkey = NULL;
    X509 *cert = NULL;
    STACK_OF(X509) *ca = NULL;

    OpenSSL_add_all_algorithms();
    ERR_load_crypto_strings();

    if (!PKCS12_parse(p12, password, &pkey, &cert, &ca)) {
        fprintf(stderr, "Failed to parse PKCS12 file\n");
        ERR_print_errors_fp(stderr);
        PKCS12_free(p12);
        return 1;
    }

    printf("Import successful\n");

    // Free memory
    PKCS12_free(p12);
    EVP_PKEY_free(pkey);
    X509_free(cert);
    if (ca) {
        sk_X509_pop_free(ca, X509_free);
    }

    return 0;
}
