plugins {
    java
    kotlin("jvm") version "1.3.72"
}

group = "org.example"
version = "1.0-SNAPSHOT"

repositories {
    mavenCentral()
}

dependencies {
    implementation(kotlin("stdlib-jdk8"))
    testCompile("junit", "junit", "4.12")

    implementation("com.amazonaws:aws-lambda-java-core:1.2.1")
    implementation("com.amazonaws:aws-lambda-java-events:2.2.8")
    implementation("com.amazonaws:aws-lambda-java-log4j2:1.2.0")
}

tasks {
    compileKotlin {
        kotlinOptions.jvmTarget = "1.8"
    }
    compileTestKotlin {
        kotlinOptions.jvmTarget = "1.8"
    }
}

task<Zip>("buildZip") {
    dependsOn("build")
    archiveFileName.set("main.zip")
    destinationDirectory.set(file("$buildDir/dist"))
    exclude("META-INF")
    from("$buildDir/classes/kotlin/main")
    into("lib") {
        from(configurations.runtimeClasspath)
    }
}
