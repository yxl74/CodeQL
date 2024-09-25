import java
import semmle.code.java.dataflow.DataFlow
import semmle.code.xml.AndroidManifest
import semmle.code.java.frameworks.android.Android

/** Service Class */
class ServiceClass extends RefType {
    ServiceClass() {
        this.getASupertype*().hasQualifiedName("android.app", "Service")
    }
}

/** Holds if the service is statically declared in AndroidManifest.xml */
predicate isStaticallyDeclaredService(ServiceClass service, AndroidComponentXmlElement svc) {
    svc instanceof AndroidServiceXmlElement and
    svc.getComponentName() = ["." + service.getName(), service.getQualifiedName()]
}

/** A method that starts a service dynamically */
class StartServiceMethod extends Method {
    StartServiceMethod() {
        this.getDeclaringType().getASupertype*().hasQualifiedName("android.content", "Context") and
        this.hasName(["startService", "startForegroundService"])
    }
}

/** Holds if the service is dynamically started in Code */
predicate isDynamicallyStartedService(ServiceClass service, MethodAccess ma) {
    exists(StartServiceMethod m, ClassInstanceExpr newIntent |
        ma.getMethod() = m and
        newIntent.getConstructedType().hasQualifiedName("android.content", "Intent") and
        newIntent.getArgument(1).(TypeLiteral).getTypeName() = service.getQualifiedName() and
        DataFlow::localFlow(DataFlow::exprNode(newIntent), DataFlow::exprNode(ma.getArgument(0)))
    )
}

from ServiceClass service, string declarationType, string location
where 
    (
        exists(AndroidComponentXmlElement svc | 
            isStaticallyDeclaredService(service, svc) and
            declarationType = "statically" and
            location = svc.getFile().getAbsolutePath()
        )
        or
        exists(MethodAccess ma |
            isDynamicallyStartedService(service, ma) and
            declarationType = "dynamically" and
            location = ma.getFile().getAbsolutePath()
        )
    )
select
    service.getQualifiedName(),
    declarationType,
    service.getPackage().getName(),
    "Declared " + declarationType + " at " + location
