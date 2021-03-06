import org.jetbrains.kotlin.gradle.targets.js.yarn.yarn
import org.jetbrains.kotlin.gradle.tasks.KotlinCompile

plugins {
	id("org.springframework.boot") version "2.2.5.RELEASE"
	id("io.spring.dependency-management") version "1.0.9.RELEASE"
	kotlin("jvm") version "1.3.61"
	kotlin("plugin.spring") version "1.3.61"

	// yarnを実行するプラグイン
	id("com.moowork.node") version "1.3.1"
}

group = "com.github.ackintosh"
version = "0.0.1-SNAPSHOT"
java.sourceCompatibility = JavaVersion.VERSION_11

repositories {
	mavenCentral()
}

dependencies {
	implementation("org.springframework.boot:spring-boot-starter-web")
	implementation("com.fasterxml.jackson.module:jackson-module-kotlin")
	implementation("org.jetbrains.kotlin:kotlin-reflect")
	implementation("org.jetbrains.kotlin:kotlin-stdlib-jdk8")
	testImplementation("org.springframework.boot:spring-boot-starter-test") {
		exclude(group = "org.junit.vintage", module = "junit-vintage-engine")
	}

	//////////////////////////////
	/// graphql-java-kickstart ///
	//////////////////////////////
	implementation("com.graphql-java-kickstart:graphql-spring-boot-starter:6.0.1")
	implementation("com.graphql-java-kickstart:graphiql-spring-boot-starter:6.0.1")
}

tasks {
	"build" {
		// スキーマに定義した型のクラスを自動生成する
		// see codegen.yml
		// NOTE: Kotlinのクラスが生成されないのでひとまずコメントアウト
		//       (TypeScriptだと生成されたので、Kotlinジェネレータの問題?)
		// dependsOn(yarn)
	}
}

tasks.withType<Test> {
	useJUnitPlatform()
}

tasks.withType<KotlinCompile> {
	kotlinOptions {
		freeCompilerArgs = listOf("-Xjsr305=strict")
		jvmTarget = "1.8"
	}
}
