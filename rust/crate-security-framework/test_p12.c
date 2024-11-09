#include <stdio.h>
#include <stdlib.h>
#include <CoreFoundation/CoreFoundation.h>
#include <Security/Security.h>

int main() {
    const char *filename = "server.p12";
    const char *password = "bark";

    // Read the PKCS#12 file
    CFDataRef pkcs12Data = NULL;
    {
        FILE *fp = fopen(filename, "rb");
        if (!fp) {
            perror("Cannot open file");
            return 1;
        }
        fseek(fp, 0, SEEK_END);
        long fileSize = ftell(fp);
        rewind(fp);

        unsigned char *buffer = (unsigned char *)malloc(fileSize);
        if (fread(buffer, 1, fileSize, fp) != fileSize) {
            perror("Failed to read file");
            fclose(fp);
            free(buffer);
            return 1;
        }
        fclose(fp);

        pkcs12Data = CFDataCreate(NULL, buffer, fileSize);
        free(buffer);
    }

    // Set PKCS#12 import options
    CFStringRef passwordStr = CFStringCreateWithCString(NULL, password, kCFStringEncodingUTF8);
    const void *keys[] = { kSecImportExportPassphrase };
    const void *values[] = { passwordStr };
    CFDictionaryRef options = CFDictionaryCreate(NULL, keys, values, 1, NULL, NULL);

    // Import the PKCS#12 file
    CFArrayRef items = NULL;
    OSStatus status = SecPKCS12Import(pkcs12Data, options, &items);

    // Process the result
    if (status == errSecSuccess && CFArrayGetCount(items) > 0) {
        CFDictionaryRef identityAndTrust = CFArrayGetValueAtIndex(items, 0);
        SecIdentityRef identity = (SecIdentityRef)CFDictionaryGetValue(identityAndTrust, kSecImportItemIdentity);
        SecCertificateRef certificate = NULL;
        SecKeyRef privateKey = NULL;

        // Retrieve the certificate
        if (identity) {
            OSStatus certStatus = SecIdentityCopyCertificate(identity, &certificate);
            if (certStatus == errSecSuccess) {
                CFStringRef certSummary = SecCertificateCopySubjectSummary(certificate);
                char certName[256];
                CFStringGetCString(certSummary, certName, sizeof(certName), kCFStringEncodingUTF8);
                printf("Certificate Subject: %s\n", certName);
                CFRelease(certSummary);
                CFRelease(certificate);
            }
        }

        // Retrieve the private key
        if (identity) {
            OSStatus keyStatus = SecIdentityCopyPrivateKey(identity, &privateKey);
            if (keyStatus == errSecSuccess) {
                printf("Private key imported successfully\n");
                CFRelease(privateKey);
            }
        }

        printf("Import successful\n");
    } else {
        CFStringRef errorMessage = SecCopyErrorMessageString(status, NULL);
        char errorStr[256];
        CFStringGetCString(errorMessage, errorStr, sizeof(errorStr), kCFStringEncodingUTF8);
        fprintf(stderr, "Failed to import PKCS12 file: %s (Error code: %d)\n", errorStr, (int)status);
        CFRelease(errorMessage);
    }

    // Release memory
    if (items) CFRelease(items);
    CFRelease(options);
    CFRelease(passwordStr);
    CFRelease(pkcs12Data);

    return 0;
}
